/*
 * 
 * Copyright(C) 2006, EU's Snocer software copyright will apply to this software(It should be GPL -
 * Gnu public licence).
 *
 * Functions included in this file are designed to enable the RTP_relay proxy server to work in two 
 * modes: master-mode and backup-mode, and to perform modes switching from backup mode to master mode 
 * upon receiving a take-over command.
 * For doing these, codes have also been added to the main.c file to facilitate the two modes working
 * and switching. 
 *
 * In master mode, the RTP-relay proxy server performs RTP traffic relay as normal.
 * In backup mode, the RTP-relay proxy server only duplicate the sessions information received from a master
 * RTP-relay proxy server to prepare to take over the master server's relay tasks in case the master 
 * RTP-relay proxy server stopped to function. In backup mode, the RTP-relay proxy server do not 
 * relay any RTP traffic, it only take information from the high availability daemon(HAD) and keep all 
 * sessions information that the HAD is managing.
 *
 * Pre-condition:
 * The mode switch is working under the following assumptions: 
 * 
 *     1.)   bmode = 0.  
 *     2.)   optional commands are ignored.  
 *
 * The complete RTP-relay proxy server codes can be found on the Snocer project web side.
 * 
 *
 * 
 * 
 *                                                        Juntong Liu (juntong.liu@embiron.com)
 *
 *                                                                                   2006.08.21
 */

#include <sys/types.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/un.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <setjmp.h> 
#include <string.h>
#include <strings.h>
#include <unistd.h>
#include <net/if_arp.h>
#include <sys/ioctl.h>
#include <linux/sockios.h>
#include <linux/if.h>
#include <sys/times.h>

#include "rtpp_defines.h"
#include "rtpp_log.h"
#include "rtpp_session.h"
#include "rtpp_util.h"

extern int controlfd;
extern struct sockaddr_storage craddr; 
extern jmp_buf returnp_1;
extern struct sockaddr_in *sbindaddr[2];
extern struct sockaddr *bindaddr[2]; 
extern lastport[2];
extern unsigned long long sessions_created;
extern int oprt_mode;
extern LIST_HEAD(, rtpp_session) session_set;

void notice_had(struct rtpp_session *);
void switch_to_master_mode(char *);
void process_fmap_cmd(char **argv, int argc, char *buf, char *cookie);
static void fill_peer_address(struct rtpp_session *, 
			      struct sockaddr **, char **);
static int address_takeover(void);
void ask_moresource(void);
extern void rebuild_tables(void);



/* 
 * This function is called every time when the RTP-relay operating in master mode has a RTP
 * session, but it is time out and to be deleted. This function will form a "delete" command to send
 * to the high availability daemon. The HAD will pass this message to the backup RTP-relay server to 
 * delete the same session. So, both of them can be synchronized. 
 */ 
void notice_had(struct rtpp_session *sp)
{
  static int cookie;
  int ret;
  char cmd_buf[256];
  char *sep = "\r\n\t ";

  srand(time(NULL)|cookie);
  cookie = rand();

  sprintf(cmd_buf, "%d%s%c%s%s%s%s%s%c", cookie, sep, 'D', sep, 
	  sp->call_id, sep, sp->tag, sep, '0');                 /* I hope this is a char 0, not an integer 0 */

  ret = sendto(controlfd, cmd_buf, strlen(cmd_buf)+1, 0, sstosa(&craddr), 
	       sizeof(craddr));
  if(ret < 0)
    rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send delete command to HAD");
 
  return;

}



/* 
 * This function is called when processing FL and FU command to fill
 * a socket address pair into the session block.
 *
 * Input:
 *        remote_saddr --- sockaddr structures pair.
 *        spa          --- point to the session block. 
 *        argv         --- command and options                
 *
 * Output:
 *        nothing, just fill the addr in the session block.
 */
static void fill_peer_address(struct rtpp_session *spa, 
		       struct sockaddr **remote_saddr, char **argv)
{
  int i, pindex;

  if (argv[0][1] == 'L' || argv[0][1] == 'l')  
    pindex = 0;           
  
  else if(argv[0][1] == 'U' || argv[0][1] == 'u')
    pindex = 1;
  
  if(remote_saddr[0] != NULL && remote_saddr[1] != NULL)
  {
      
	      rtpp_log_write(RTPP_LOG_INFO, spa->log, "In backup mode: pre-filling %s's address "
			     "with %s:%s", (pindex == 0) ? "callee" : "caller", argv[2], argv[3]);
	      
	      if (spa->addr[pindex] != NULL)
		free(spa->addr[pindex]);
	      spa->addr[pindex] = remote_saddr[0];   
	      
	      remote_saddr[0] = NULL;
	      
	      if (!(spa->rtcp->addr[pindex] != NULL &&
		    SA_LEN(remote_saddr[1]) == SA_LEN(spa->rtcp->addr[pindex]) &&
		    memcmp(remote_saddr[1], spa->rtcp->addr[pindex], SA_LEN(remote_saddr[1])) == 0)) 
              {
		if (spa->rtcp->addr[pindex] != NULL)
		  free(spa->rtcp->addr[pindex]);
		spa->rtcp->addr[pindex] = remote_saddr[1]; 
		
		remote_saddr[1] = NULL;
	      }
    
  }
  

  for (i = 0; i < 2; i++)  
    if (remote_saddr[i] != NULL)
      free(remote_saddr[i]);
  
  return;

}


/* 
 * This function processes the FU and FL commands. This two commands should be received
 * when the RTP-relay server working in backup mode.
 * The FL corresponding to the original L(request) command, it will cause new
 * session blocks to be created and put onto the list without create any socket.
 * The command come with additional master's local IP address and  port number info.
 * The FU command is corresponding to L(response) command. It put another port number
 * in the already created session blocks.
 *
 */
void process_fmap_cmd(char **argv, int argc, char *buf, char *cookie)
{
  char reply_buf[2048];
  int ret, index;
  char *sep = "\r\n\t "; 
  struct rtpp_session *spa, *spb, *rsp;
  struct sockaddr *remote_saddr[2];  
  struct sockaddr_storage tia;       
  unsigned long int local_port;
  int i, n, pindex;
  struct in_addr addrN;

    /* process a cmd */
    if(argc < 7 || argc > 8){     
      sprintf(reply_buf, "%s%s%s%s%s", cookie, sep, 
	      buf, sep, "Force mapping command error syntx error, EO\n");
      goto got_error;
    }

    /* calculate the local port number */
    //  local_port = (unsigned long)htons((unsigned short)strtoul(argv[7], NULL, 10));
    local_port = strtoul(argv[7], NULL, 10);
    if(local_port < PORT_MIN || local_port > PORT_MAX){
      sprintf(reply_buf, "%s%s%s%s%s", cookie, sep, buf, sep, "Command port error, EO!");
      goto got_error;
    }

    if ((n = resolve(sstosa(&tia), PF_INET, argv[2], argv[3],
		     AI_NUMERICHOST)) == 0) 
    {
      if (!ishostnull(sstosa(&tia))) 
      {  
	for (i = 0; i < 2; i++) 
        {            
	  remote_saddr[i] = malloc(SS_LEN(&tia));
          
	  if (remote_saddr[i] == NULL) 
	    {
	      err(1, "Out of memory\n");
	      longjmp(returnp_1, -1);
	    }
          
	  memcpy(remote_saddr[i], &tia, SS_LEN(&tia)); 
	}
        
	n = ntohs(satosin(remote_saddr[1])->sin_port);           
	satosin(remote_saddr[1])->sin_port = htons(n + 1);   
      }
    } 
    else {
        
      rtpp_log_write(RTPP_LOG_ERR, glog, "getaddrinfo: %s",
		     gai_strerror(n));
      sprintf(reply_buf, "%s", "Getaddrinfo error\n");
      
      goto got_error;
    }

      /* prepare for the address, assume no bmode */
      if(sbindaddr[0] == NULL)
      {    
	sbindaddr[0] = (struct sockaddr_in *)malloc(sizeof(struct sockaddr_in));
        
	if(sbindaddr[0] == NULL)
	  goto out_of_memory;
	
        inet_aton(argv[6], &addrN);  
	sbindaddr[0]->sin_family = PF_INET;
	sbindaddr[0]->sin_addr.s_addr = addrN.s_addr;
	sbindaddr[0]->sin_port = 0;  
      };

      //if(lastport[0] < local_port)
      lastport[0] = local_port + 1 ;    

    /* Now, process the FL command. Note, two letters command disable optional commands */
    if(argv[0][1] == 'L' || argv[0][1] == 'l')
    {
      for(spa = LIST_FIRST(&session_set); spa != NULL; spa = rsp) 
      {
        rsp = LIST_NEXT(spa, link);

	if(spa->rtcp == NULL || spa->call_id == NULL || 
	   strcmp(spa->call_id, argv[1]) != 0)
	  continue;

	if(spa->complete == 0)
        {  
	  /* here we do not create socket pair, but record the port only  */
	  spa->fds[1] = -1;          
	  spa->rtcp->fds[1] = -1;
          spa->ports[1] = local_port;
	  spa->rtcp->ports[1] = local_port + 1;
	  spa->complete = spa->rtcp->complete = 1;
	}

	spa->weak[1] = 0;
	spa->weak[0] = 0;
	spa->ttl = SESSION_TIMEOUT; 
	fill_peer_address(spa, remote_saddr, argv);
	
	/* LOG INFO */
	rtpp_log_write(RTPP_LOG_INFO, "Callee's socket address is filled using addr = %s, port=%s\n", 
		argv[2], argv[3]);

	sprintf(reply_buf, "%s%s%c%s%s%s%s", cookie, sep, 'F', sep, argv[6], sep, argv[7]);

	ret = sendto(controlfd, reply_buf, strlen(reply_buf)+1, 0, sstosa(&craddr), 
		     sizeof(craddr));
        
      if(ret < 0)       
	  rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send reply!");
	longjmp(returnp_1, -1);
  
      }
    }      
    else if(argv[0][1] == 'U' || argv[0][1] == 'u')
    {    
      /* really need a function to do the job when re-write the handle cmd function */ 
      spa = malloc(sizeof(*spa)); 
      
      if (spa == NULL) 
      {
	err(1, "Out of memory!\n");
	goto out_of_memory;
      }

      /* Create a session block for RTCPs */
      spb = malloc(sizeof(*spb));
      if (spb == NULL) 
      {
	err(1, "Out of memory!\n");
	goto out_of_memory;
      }
      memset(spa, 0, sizeof(*spa));
      memset(spb, 0, sizeof(*spb));
      
      for (i = 0; i < 2; i++)
	spa->fds[i] = spb->fds[i] = -1;

      spa->call_id = strdup(argv[1]);   /* set the call id */
      
      if (spa->call_id == NULL) 
      {
	err(1, "Error setting call-id!\n");
	goto out_of_memory;
      }
      spb->call_id = spa->call_id;
      spa->tag = strdup(argv[4]);     /* set the spa->tag to from_tag  */
      
      if (spa->tag == NULL) 
      {
	err(1, "Error setting session tag!\n");
	goto out_of_memory;
      }
      spb->tag = spa->tag;
      
      for (i = 0; i < 2; i++) 
      {
	spa->rrcs[i] = NULL;
	spb->rrcs[i] = NULL;  
	/* for now */
	//	spa->laddr[i] = bindaddr[0];
	//	spb->laddr[i] = bindaddr[0];
        spa->laddr[i] = (struct sockaddr *)sbindaddr[0];
        spb->laddr[i] = (struct sockaddr *)sbindaddr[0];
	spa->canupdate[i] = 1;      /* number one, not i */
	spb->canupdate[i] = 1;
      }

      spa->strong = 1;
      spa->fds[0] = -1; 
      spb->fds[0] = -1; 
      spa->ports[0] = local_port;      
      spb->ports[0] = local_port + 1;  
      spa->ttl = SESSION_TIMEOUT; 
      spb->ttl = -1;
      spa->log = rtpp_log_open("rtpproxy", spa->call_id, 0);
      spb->log = spa->log;
      spa->rtcp = spb;
      spb->rtcp = NULL;
      spa->rtp = NULL;
      spb->rtp = spa;
      fill_peer_address(spa, remote_saddr, argv);
      
      /* LOG INFO */
      rtpp_log_write(RTPP_LOG_INFO, "Caller's sockaddr is filled: address: %s, port: %s\n", 
		     argv[2], argv[3]);

      LIST_INSERT_HEAD(&session_set, spa, link);             
      LIST_INSERT_HEAD(&session_set, spb, link);
     
      sessions_created++;
      
      rtpp_log_write(RTPP_LOG_INFO, spa->log, "new session on a port %d created, "
		     "tag %s", local_port, argv[4]);


      sprintf(reply_buf, "%s F %s %s", cookie, argv[6], argv[7]);

      ret = sendto(controlfd, reply_buf, strlen(reply_buf)+1, 0, sstosa(&craddr), 
		   sizeof(craddr));

      if(ret < 0)       
	  rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send reply!");
      longjmp(returnp_1, -1);
      
    }
    else {
      sprintf(reply_buf, "%s%s%s", cookie, sep, "EO");
      goto got_error;
    }
      
 out_of_memory:
    rtpp_log_write(RTPP_LOG_ERR, glog, "can't allocate memory");

 got_error:
                                 
    for (i = 0; i < 2; i++)
    {
      if (remote_saddr[i] != NULL)
          free(remote_saddr[i]);
    }
 
    if (spa != NULL) 
    {
      if (spa->call_id != NULL)
	free(spa->call_id);
      free(spa);
    }
 
    if (spb != NULL)
      free(spb);

    ret = sendto(controlfd, reply_buf, strlen(reply_buf)+1, 0, sstosa(&craddr), 
	       sizeof(craddr));
      if(ret < 0)       
	  rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send reply!");
    longjmp(returnp_1, -1);

}

#include <sys/resource.h>
void ask_moresource(void)
{
  struct rlimit this_limit;

  if(getrlimit(RLIMIT_NOFILE, &this_limit))
  {
    rtpp_log_write(RTPP_LOG_INFO, glog, "Can not get resource limit!");
    return;
  }

  printf("The rlim_cur = %d, rlim_max = %d\n", this_limit.rlim_cur, this_limit.rlim_max);

  if(this_limit.rlim_cur < 30000)
  {
    this_limit.rlim_cur = 30200;
    this_limit.rlim_max = 30200;
 
    if(setrlimit(RLIMIT_NOFILE, &this_limit))
    {
      rtpp_log_write(RTPP_LOG_INFO, glog, "Can not set resource limit!");
      return;
    }
  }

  /* DEBUGG ------------------ */
  if(getrlimit(RLIMIT_NOFILE, &this_limit))
  {
    rtpp_log_write(RTPP_LOG_INFO, glog, "Can not get resource limit!");
    return;
  }
  
  printf("After set new rlim_cur = %d, rlim_max = %d\n", this_limit.rlim_cur, this_limit.rlim_max);

}


/* 
 * This function is called when receiving "take over" command to switches the RTP-relay server 
 * from backup mode to master mode to perform normal RTP relay functions.
 * A real takeover need to replace our IP and MAC address with the failur master server's
 * IP and MAC addresses. 
 * We already know the master's IP address. Maybe the had can carry the master server's
 * MAC address in the 'T' command.  
 * 
 */
void switch_to_master_mode(char *cookie)
{
  struct rtpp_session *spa, *rsp;
  struct sockaddr_in listen_socket;           /* two listen sockets need to be created  */
  int fds[2], i, n, ret;                      /* two listen fds neend to be created     */
  int retv;
  int num_sock;  /* DEBUG */
  char rep_buf[128], *sep="\r\n\t ";

  /* TEST TEST TEST TEST */
#if 0
  int num_session;
  struct tms begin_t, end_t;
  bzero(&begin_t, sizeof(struct tms));
  bzero(&end_t, sizeof(struct tms));
    times(&begin_t);    /* measure the mode switch time */
    printf("Mode switch begining time is: %ld\n", begin_t.tms_utime + begin_t.tms_stime +
	   begin_t.tms_cutime + begin_t.tms_cstime);
#endif
 
  /* first thing first */
  oprt_mode = 0;

  /* Un-comment the following two lines when run in real-environment.
   * If we replace our MAC address with the master's MAC address, we have 
   * to know it. Maybe the 'T' command can carry it. The HAD can get the
   * master server's MAC address through a ARP query.  
   */ 
  //if(address_takeover()<0)           
  // rtpp_log_write(RTPP_LOG_ERR, glog, "Error, can not set address!\n");

  /* have a log */
  rtpp_log_write(RTPP_LOG_INFO, glog, "Now switched to %s mode.\n", 
		 (oprt_mode == 0)? "master":"backup");   

  for(spa = LIST_FIRST(&session_set); spa != NULL; spa = rsp) 
  {
    rsp = LIST_NEXT(spa, link);
    //num_session++;            /* TEST TEST TEST */
  
    for(i = 0; i<2; i++)
    {
      fds[i] = socket(PF_INET, SOCK_DGRAM, 0);
    
      if(fds[i] == -1)
      {
	rtpp_log_write(RTPP_LOG_INFO, glog, "Can't create %s socket", "IPv4");
	//perror("Error creating socket\n");
	n = -1;
	goto error1;
      }
      
      memcpy(&listen_socket, spa->laddr[i], sizeof(struct sockaddr_in));
      listen_socket.sin_port = htons(spa->ports[i]);
      //listen_socket.sin_port = spa->ports[i];
      
      
#if 0
      {   
	struct in_addr addrn;
	struct sockaddr_in *sinp;
	
	rtp_log_write(RTPP_LOG_INFO, glog, "bind to port: %d, lastport=%d\n", 
		      listen_socket.sin_port, lastport[0]);
	
	if(spa->addr[i])
	  {
	    sinp = (struct sockaddr_in *)spa->addr[i];
	    addrn.s_addr = sinp->sin_addr.s_addr;
	    rtp_log_write(RTP_LOG_INFO, glog, "This session's %s IP: %s\n", (i == 0)? "caller":"callee", 
			  inet_ntoa(addrn));
	  }else
	  rtp_log_write(RTP_LOG_INFO, glog, "Session address is not filled!\n");
      }
#endif 
      //num_sock++;
      //printf(" %d; ", num_sock);  /* DEBUG */

      if(bind(fds[i], (struct sockaddr*)&listen_socket, sizeof(struct sockaddr_in)) != 0)
      {
	if(errno != EADDRINUSE && errno != EACCES)
        {
	  rtpp_log_ewrite(RTPP_LOG_ERR, glog, "Can't bind to the %s prot %d",
			  "IPV4", listen_socket.sin_port);
	  goto error1;
	  n = -2;
	}
        else{
	  retv = -2;
	  goto error1;
	}
      }
      
      /* fill the listen ports */
      spa->fds[i] = fds[i]; 
      //rebuild_tables();
    }
  }
  
  rebuild_tables();
  //printf("Number of session is: %d\n", num_session);   /* TEST TEST TEST TEST */

  ret = sendto(controlfd, cookie, strlen(cookie)+1, 0, sstosa(&craddr), 
	       sizeof(craddr));
  if(ret < 0)       
	rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send reply!");

  /* TEST TEST TEST TEST */
#if 0
    times(&end_t);   /* measure the mode switch time */    
    printf("Mode swithing for 6000 ports use %ld clock ticks\n", end_t.tms_utime +
	   end_t.tms_stime + end_t.tms_cutime + end_t.tms_cstime);
#endif 
  longjmp(returnp_1, -1);
  
 
 error1:
  printf("DBG::: We got an ERROR\n");   /* DEBUGG */
  for (i= 0; i<2; i++)
  {
    if(fds[i] != -1)
    {
      close(fds[i]);
      fds[i] = -1;
    }    
  }
  rebuild_tables();        /* NEW ADDED */
  sprintf(rep_buf, "%s, %s", cookie, (n==-1)?"EO - Can not create socket":"EO - Cannot bind");
  
  ret = sendto(controlfd, rep_buf, strlen(rep_buf)+1, 0, sstosa(&craddr), 
	       sizeof(craddr));
  if(ret < 0)       
	rtpp_log_write(RTPP_LOG_ERR, glog, "Error: Can not send reply!");
  longjmp(returnp_1, -1);
 
}


