-------------------------------- MODULE hlc --------------------------------

EXTENDS Integers
CONSTANT N, STOP, EPSILON
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks naive algorithm

--algorithm hlc {
variable pt = [j \in Procs |-> 0], l = [j \in Procs |-> 0], c = [j \in Procs |-> 0], 
         mailbox_l=[j \in Procs |-> 0], mailbox_c=[j \in Procs |-> 0], random=0, temp=0;


    fair process (j \in Procs)
    { J0: while (pt[self] < STOP)
        { either \* local or receive event
            J1:{ \* physical clocks cannot diverge more than EPSILON
        
                    await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                    pt[self] := pt[self] +1;
            
                    temp:=l[self];
                    l[self] := SetMax({temp,mailbox_l[self], pt[self]});
            
                    if(l[self]=temp)
                    {
                        if(temp=mailbox_l[self])
                            c[self]:=SetMax({c[self],mailbox_c[self]})+1;
                    }
            
                    else if(l[self]=temp)
                        c[self]:=c[self]+1;
            
                    else if(l[self]=mailbox_l[self])
                        c[self]:=mailbox_c[self]+1;
            
                    else
                        c[self]:=0;
               }
         or \* send event
            J2:{ \* physical clocks cannot diverge more than EPSILON
                  await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                  pt[self] := pt[self] +1;
                  temp:=l[self];
                  l[self] := SetMax({temp,pt[self]});
            
                  if(l[self]=temp)
                    c[self]:=c[self]+1;
                  
                  else
                    c[self]:=0;
                
                  random:=CHOOSE i \in Procs: i /= self;
                  mailbox_l[random]:=l[self];
                  mailbox_c[random]:=c[self];
                }
            }
      }
}
    
    *)
\* BEGIN TRANSLATION
VARIABLES pt, l, c, mailbox_l, mailbox_c, random, temp, pc

vars == << pt, l, c, mailbox_l, mailbox_c, random, temp, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ l = [j \in Procs |-> 0]
        /\ c = [j \in Procs |-> 0]
        /\ mailbox_l = [j \in Procs |-> 0]
        /\ mailbox_c = [j \in Procs |-> 0]
        /\ random = 0
        /\ temp = 0
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "J1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "J2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, l, c, mailbox_l, mailbox_c, random, temp >>

J1(self) == /\ pc[self] = "J1"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
            /\ temp' = l[self]
            /\ l' = [l EXCEPT ![self] = SetMax({temp',mailbox_l[self], pt'[self]})]
            /\ IF l'[self]=temp'
                  THEN /\ IF temp'=mailbox_l[self]
                             THEN /\ c' = [c EXCEPT ![self] = SetMax({c[self],mailbox_c[self]})+1]
                             ELSE /\ TRUE
                                  /\ c' = c
                  ELSE /\ IF l'[self]=temp'
                             THEN /\ c' = [c EXCEPT ![self] = c[self]+1]
                             ELSE /\ IF l'[self]=mailbox_l[self]
                                        THEN /\ c' = [c EXCEPT ![self] = mailbox_c[self]+1]
                                        ELSE /\ c' = [c EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "J0"]
            /\ UNCHANGED << mailbox_l, mailbox_c, random >>

J2(self) == /\ pc[self] = "J2"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
            /\ temp' = l[self]
            /\ l' = [l EXCEPT ![self] = SetMax({temp',pt'[self]})]
            /\ IF l'[self]=temp'
                  THEN /\ c' = [c EXCEPT ![self] = c[self]+1]
                  ELSE /\ c' = [c EXCEPT ![self] = 0]
            /\ random' = (CHOOSE i \in Procs: i /= self)
            /\ mailbox_l' = [mailbox_l EXCEPT ![random'] = l'[self]]
            /\ mailbox_c' = [mailbox_c EXCEPT ![random'] = c'[self]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ J1(self) \/ J2(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == (\A k \in Procs: l[k] >= pt[k])
Sync == (\A k,m \in Procs: pt[k] <= pt[m]+EPSILON)
Bounded == (\A k \in Procs: l[k] < pt[k] + N*(EPSILON+1))
Bounded_C == (\A k \in Procs: c[k] <= N*(EPSILON+1))
=======================================================
Vidyadhar Reddy Annapureddy(vidyadhar.reddy23@gmail.com)

The HLC algorithm introduces a new variable to track the difference between logical time and physical time. Initially the system starts with the 
logical clock and c set to 0 for all processes. When a send event occurs at a process, the logical time is updated to maximum of the logical time 
and physical time. If the logical time is not updated (remains the same), c is incremented by 1. Otherwise, it is reset to 0. It chooses a random 
process from the N processes of the system and timestamps its mailbox with its logical clock time and c. 

When a process receives a message, it updates logical clock its to maximum of its previous logical clock, message timestamp and the physical time.
If its logical time is same as its previous logical time and the message timestamp, then c is set to maximum of its own c or c of message 
incremented by 1. If logical time is same as the message timestamp, c of message is incremented by 1. If logical time is same as its previous logical
time, its c is incremented by 1. In any other case, it is reset to 0. 
