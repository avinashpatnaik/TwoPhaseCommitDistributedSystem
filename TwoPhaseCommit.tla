------------------------------- MODULE -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,         \* The set of participating resource managers RM=1..3 
         TMMAYFAIL      \* Whether TM may fail

(***************************************************************************
--fair algorithm 2PC {
variable rmState = [rm \in RM |-> "working"],
         tmState = "init";
  
define {
   canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared"} 
   canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted"} 
}



  fair process (RManager \in RM) {
RS:  while (rmState[self] \in {"working", "prepared"}) { 
        either { 
           await rmState[self] = "working";
           rmState[self] := "prepared" ; } 
        or { 
           await rmState[self]="prepared" /\ tmState="commit";
RC:        rmState[self] := "committed";}
        or {
           await rmState[self]="working" 
            \/  (rmState[self]="prepared" /\ tmState="abort");
RA:        rmState[self] := "aborted";}  
     }                 
  }


   
  fair process (TManager=0) {
TM:  either 
      { await canCommit;
        tmState := "commit";
F1:     if (TMMAYFAIL) tmState := "unavailable";}         
     or 
      { await canAbort;
        tmState := "abort";
F2:     if (TMMAYFAIL) tmState := "unavailable";}  
  }



}

***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, pc

(* define statement *)
canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared"}
canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted"}


vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TM"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             /\ pc' = [pc EXCEPT ![self] = "RS"]
                          \/ /\ rmState[self]="prepared" /\ tmState="commit"
                             /\ pc' = [pc EXCEPT ![self] = "RC"]
                             /\ UNCHANGED rmState
                          \/ /\      rmState[self]="working"
                                \/  (rmState[self]="prepared" /\ tmState="abort")
                             /\ pc' = [pc EXCEPT ![self] = "RA"]
                             /\ UNCHANGED rmState
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RC(self) == /\ pc[self] = "RC"
            /\ rmState' = [rmState EXCEPT ![self] = "committed"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED tmState

RA(self) == /\ pc[self] = "RA"
            /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED tmState

RManager(self) == RS(self) \/ RC(self) \/ RA(self)

TM == /\ pc[0] = "TM"
      /\ \/ /\ canCommit
            /\ tmState' = "commit"
            /\ pc' = [pc EXCEPT ![0] = "F1"]
         \/ /\ canAbort
            /\ tmState' = "abort"
            /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unavailable"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unavailable"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TM \/ F1 \/ F2

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION






Consistency ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

Completed == <> (\A rm \in RM : rmState[rm] \in {"committed","aborted"}) 

NotCommitted == \A rm \in RM : rmState[rm] # "committed" 

TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "commit", "abort", "unavailable"}

=============================================================================
\* Modification History
\* Last modified Tue Jun 02 15:47:07 EDT 2020 by Avinash
\* Created Tue Jun 02 15:29:01 EDT 2020 by Avinash
