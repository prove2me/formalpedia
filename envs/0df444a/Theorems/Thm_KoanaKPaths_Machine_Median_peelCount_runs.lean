-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Median_peelCount_runs
-- name    : KoanaKPaths.Machine.Median.peelCount_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:17.416594+00:00
-- url     : https://prove2.me/theorems/832c4b09-d939-4de5-84e0-a61a040e9035
-- title:
--   Peel two unary counters and save their common prefix
-- statement:
--   Let two unary counters initially contain $c$ observed markers and $t$ threshold markers, and suppose the saved-marker stack is empty. The peeling program consumes all observed markers and transforms the other counters according to
--   $$
--   \operatorname{Count}'=0,\qquad\operatorname{Threshold}'=\max(t-c,0),\qquad\operatorname{Saved}'=\min(t,c).
--   $$
--   These equations describe marker counts; every counter's original tail remains in place and all unrelated stacks are preserved. The charged running time is at most
--   $$
--   60c+30.
--   $$
--   Thus the program records exactly how much of the threshold was removed, including the cases $c=0$, $t=0$ and $c>t$. It is the reversible comparison primitive used in the native median-search threshold test.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/UnaryCompare.lean, line 18; source snapshot SHA-256 0eecc76db7a82fdac4f8982813d1e20f456e7467adb03ad2cbcb294bfd46b255.

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

theorem KoanaKPaths.Machine.Median.peelCount_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (c t : Nat)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.replicate.{0} NLogN.Item c NLogN.Item.mark))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark)),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.peelCount s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Median.Threshold
        (@List.replicate.{0} NLogN.Item (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t c)
          NLogN.Item.mark))
      KoanaKPaths.Machine.Median.Saved
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@Min.min.{0} Nat instMinNat t c) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) c)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
