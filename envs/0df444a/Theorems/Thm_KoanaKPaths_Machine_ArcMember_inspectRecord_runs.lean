-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_ArcMember_inspectRecord_runs
-- name    : KoanaKPaths.Machine.ArcMember.inspectRecord_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:58.126121+00:00
-- url     : https://prove2.me/theorems/a8f6df11-6e03-4018-900c-fb51abeb7d3b
-- title:
--   Inspect one arc record and accumulate a membership flag
-- statement:
--   Let an arc database begin with the record $(u,v)$, let the query registers contain $(q_u,q_v)$, and let the current membership flag be $f$. With the two comparison scratch registers empty, the native record-inspection program removes this record from the database, pushes it onto the back stack, and replaces the flag by
--   $$
--   f'=f\lor(u=q_u\land v=q_v).
--   $$
--   All query values, stack tails, input position and output are preserved. Its charged running time is at most
--   $$
--   2C_{\rm rec}(u,v)+C_{=}(u,q_u)+C_{=}(v,q_v)+200,
--   $$
--   where $C_{\rm rec}$ is the declared take/push cost for the two-integer record and $C_{=}$ is the exact integer-equality comparison cost. This is the single-record correctness and cost contract used by the graph's arc-membership scan.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArcInspect.lean, line 13; source snapshot SHA-256 128948eaf2580d1def8fde908d529f24d0f936d9d001b3f324e730c2f0383347.

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

theorem KoanaKPaths.Machine.ArcMember.inspectRecord_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (u v qu qv : Int) (f : Bool)
  (tail qtU qtV ft : List.{0} NLogN.Item)
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int v)
        (@List.cons.{0} NLogN.Item (NLogN.Item.int u) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))))
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
    KoanaKPaths.Machine.ArcMember.inspectRecord s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB tail)
        KoanaKPaths.Machine.ArcMember.Back
        (@List.cons.{0} NLogN.Item (NLogN.Item.int v)
          (@List.cons.{0} NLogN.Item (NLogN.Item.int u)
            (@List.cons.{0} NLogN.Item NLogN.Item.mark
              (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Back)))))
      KoanaKPaths.Machine.ArcMember.Found
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (Bool.toNat
              (KoanaKPaths.Machine.ArcMember.nextFound (@Decidable.decide (@Eq.{1} Int u qu) (Int.instDecidableEq u qu))
                (@Decidable.decide (@Eq.{1} Int v qv) (Int.instDecidableEq v qv)) f))))
        ft))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (KoanaKPaths.Machine.ArcMember.recordCost u v))
          (KoanaKPaths.Machine.compareCost u qu))
        (KoanaKPaths.Machine.compareCost v qv))
      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))) := by sorry
