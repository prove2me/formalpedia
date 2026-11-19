-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_ArcMember_transferRecords_exec
-- name    : KoanaKPaths.Machine.ArcMember.transferRecords_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:56.071038+00:00
-- url     : https://prove2.me/theorems/fae85040-b76e-4500-a750-f81439a93127
-- title:
--   Transfer an arc-record list with exact reversal cost
-- statement:
--   Let the distinct source and destination stacks be disjoint from the two endpoint scratch registers. Suppose the source begins with the encoded arc list $P$, followed by a tail whose first item is not an integer. The record-transfer loop consumes precisely these records and produces
--   $$
--   \operatorname{dst}_{\rm final}=\operatorname{records}(\operatorname{reverse}P)\mathbin{+\!+}\operatorname{dst}_{\rm initial}.
--   $$
--   The source becomes its original tail, both endpoint scratch stacks are restored, and every other state component is unchanged. The execution has exact cost $C(P)$, defined by
--   $$
--   C([])=30,\qquad C((u,v)::P)=2C_{\rm rec}(u,v)+30+C(P).
--   $$
--   Here $C_{\rm rec}$ is the cost of taking or pushing one two-integer arc record. This contract provides the reversible database traversal needed by membership queries.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArcTransfer.lean, line 16; source snapshot SHA-256 88b734b65f852b66410b5bc7aa82371c7f62d960816d4ae7fa7ffa6b63d7259b.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.ArcMember.transferRecords_exec :
∀ (I : List.{0} NLogN.Sym) (src dst : Fin KoanaKPaths.Machine.ArcMember.NS)
  (hsd : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src dst)
  (hsu : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src KoanaKPaths.Machine.ArcMember.U)
  (hsv : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src KoanaKPaths.Machine.ArcMember.V)
  (hdu : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) dst KoanaKPaths.Machine.ArcMember.U)
  (hdv : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) dst KoanaKPaths.Machine.ArcMember.V)
  (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (ps : List.{0} (Prod.{0, 0} Int Int)) (tail : List.{0} NLogN.Item)
  (ht : @Eq.{1} Bool (KoanaKPaths.Machine.Median.intClass (NLogN.cls (@List.head?.{0} NLogN.Item tail))) Bool.false)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records ps) tail)),
  @NLogN.IExec KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.ArcMember.transferRecords src dst) s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s src tail)
      dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records (@List.reverse.{0} (Prod.{0, 0} Int Int) ps))
        (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s dst)))
    (KoanaKPaths.Machine.ArcMember.transferCost ps) := by sorry
