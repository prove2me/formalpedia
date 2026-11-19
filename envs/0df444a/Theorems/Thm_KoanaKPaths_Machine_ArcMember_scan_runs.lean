-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_ArcMember_scan_runs
-- name    : KoanaKPaths.Machine.ArcMember.scan_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:06.343328+00:00
-- url     : https://prove2.me/theorems/4d847645-e0ce-458f-a7a7-ea7c729ac02c
-- title:
--   Correctness and bit cost of the directed-arc database scan
-- statement:
--   Let a native integer-stack state contain a marked database of ordered integer pairs $P$, readonly query endpoints $q_u,q_v$, and an existing Boolean flag $f$. Assume the scan's two comparison flags are empty and the database tail starts with a non-integer. The program consumes exactly these records, transfers them in reverse record order to its backup stack, and sets the flag to
--   $$f\lor\bigl((q_u,q_v)\in P\bigr).$$
--   It halts within the recursive bound $C(\varnothing)=30$ and $C((u,v)::P)=2\operatorname{recordCost}(u,v)+\operatorname{compareCost}(u,q_u)+\operatorname{compareCost}(v,q_v)+230+C(P)$. The input position, output, queries, and other registers are preserved. This supplies arc membership tests for the graph dynamic program.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArcScan.lean, line 20; source snapshot SHA-256 2842f14179c6eb5d701d74d391fa5b7ca5ebea3628eb80f4651cb7fe04bb1f6f.

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

theorem KoanaKPaths.Machine.ArcMember.scan_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (ps : List.{0} (Prod.{0, 0} Int Int))
  (qu qv : Int) (f : Bool) (tail qtU qtV ft : List.{0} NLogN.Item)
  (ht : @Eq.{1} Bool (KoanaKPaths.Machine.Median.intClass (NLogN.cls (@List.head?.{0} NLogN.Item tail))) Bool.false)
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records ps) tail))
  (hqu :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.QueryU)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int qu) qtU))
  (hqv :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.QueryV)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int qv) qtV))
  (hfound :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Found)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (Bool.toNat f))) ft))
  (hu :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.FlagU)
      (@List.nil.{0} NLogN.Item))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.FlagV)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.ArcMember.scan s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB tail)
        KoanaKPaths.Machine.ArcMember.Back
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.ArcMember.records (@List.reverse.{0} (Prod.{0, 0} Int Int) ps))
          (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Back)))
      KoanaKPaths.Machine.ArcMember.Found
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt (Bool.toNat (KoanaKPaths.Machine.ArcMember.scanFound qu qv ps f))))
        ft))
    (KoanaKPaths.Machine.ArcMember.scanCost qu qv ps) := by sorry
