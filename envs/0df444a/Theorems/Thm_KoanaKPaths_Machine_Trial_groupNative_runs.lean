-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_groupNative_runs
-- name    : KoanaKPaths.Machine.Trial.groupNative_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:26.196202+00:00
-- url     : https://prove2.me/theorems/237ed159-2186-4f40-ba81-4d9cfd6de270
-- title:
--   Computing one trial-group sum by native balanced accumulation
-- statement:
--   Let $O$ be a list of $m$ trial bit blocks and let $k\ge1$. In a ready native graph state, suppose the trial template contains $m$ markers, the working and copying helpers are empty, and the coin stack begins with exactly the sign streams of $O$. The group program consumes these streams and prepends one record
--   $$S=\sum_{\omega\in O}\operatorname{trialNumerator}(A,\omega).$$
--   Every other register, input position, output, and existing tail is restored. Its time is at most $mC+10000(W+2)(m+1)$, with $W=100(1+n+k)^2$ and $C=\operatorname{trialFoldBaseCost}(n,k,|A|)$. This turns multiple sketch trials into an exactly summed group numerator without repeated long-prefix addition.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GroupNative.lean, line 21; source snapshot SHA-256 e29bcf02a00eb38fa9827bfd3c366989ed401bb5510c465d93dcb845a4e1f514.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.groupNative_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
  (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (ht :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialTemplate)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)
        NLogN.Item.mark))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.trialStream n k os) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupNative s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Balanced.Records
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@List.sum.{0} Int Int.instAdd
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
            (@KoanaKPaths.Machine.Trial.numerators n k arcs os)))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Records)))
    (KoanaKPaths.Machine.Trial.groupNativeCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)
      (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)) := by sorry
