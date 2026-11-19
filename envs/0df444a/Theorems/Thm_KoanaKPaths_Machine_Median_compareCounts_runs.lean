-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Median_compareCounts_runs
-- name    : KoanaKPaths.Machine.Median.compareCounts_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:09:57.936184+00:00
-- url     : https://prove2.me/theorems/6ac3dc77-403b-4672-acb4-71c205f83ee0
-- title:
--   Compare two unary counts while preserving the threshold
-- statement:
--   Suppose the observed-count stack contains $c$ markers, the threshold stack contains $t$ markers and the saved-marker and flag stacks are empty. The native comparison program consumes the observed count, restores the threshold unchanged and leaves a marker on the flag stack exactly when the threshold has been reached:
--   $$
--   \operatorname{Flag}_{\rm final}=\begin{cases}[\operatorname{mark}]&t\le c,\\[]&t>c.\end{cases}
--   $$
--   All other state components are preserved. Its running time is at most
--   $$
--   100c+100.
--   $$
--   In particular the cost depends on the observed count, even when the threshold is larger. This is the comparison used by the median search after counting how many sample records are at most the current midpoint.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/UnaryCompare.lean, line 90; source snapshot SHA-256 0eecc76db7a82fdac4f8982813d1e20f456e7467adb03ad2cbcb294bfd46b255.

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

theorem KoanaKPaths.Machine.Median.compareCounts_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (c t : Nat)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.replicate.{0} NLogN.Item c NLogN.Item.mark))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.compareCounts s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count (@List.nil.{0} NLogN.Item))
      KoanaKPaths.Machine.Median.Flag
      (@ite.{1} (List.{0} NLogN.Item) (@LE.le.{0} Nat instLENat t c) (Nat.decLe t c)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag))
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))) c)
      (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) := by sorry
