-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Balanced_finishGroup_runs
-- name    : KoanaKPaths.Machine.Balanced.finishGroup_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:29.139329+00:00
-- url     : https://prove2.me/theorems/7eb0ee71-9f35-400f-87fc-31ced8641e61
-- title:
--   Finish a balanced sum of trial numerators
-- statement:
--   Let $x_1,\ldots,x_m$ be integers of width at most $w$. Suppose the partial-sums stack and binary occupancy stack contain the block decomposition obtained by the balanced accumulation procedure on this list. Finishing the group restores both stacks to their saved tails and prepends
--   $$
--   S=\sum_{j=1}^{m}x_j
--   $$
--   to the output-record stack. The charged time is at most
--   $$
--   C_{\rm fold}(0,\mathcal B)+34m+1000(w+m+1),
--   $$
--   where $\mathcal B$ is the current list of balanced block sums and $C_{\rm fold}$ is the declared cost of folding those blocks into the initial accumulator zero. The theorem permits arbitrary integer inputs, including an empty group. It supplies the finalization stage for group sums used by the estimator.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GroupFinish.lean, line 17; source snapshot SHA-256 ef71a41dd989ce70cc75268ba8b6782dde9a75fc11e9fae73a2eb29ba35bad78.

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

theorem KoanaKPaths.Machine.Balanced.finishGroup_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (xs : List.{0} Int)
  (pt bt : List.{0} NLogN.Item)
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int)
            (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs)))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark pt)))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Balanced.counterCode (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs))
        bt))
  (w : Nat)
  (hw :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @NLogN.IRuns KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.finishGroup s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials pt)
        KoanaKPaths.Machine.Balanced.Bits bt)
      KoanaKPaths.Machine.Balanced.Records
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@List.sum.{0} Int Int.instAdd
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) xs))
        (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Records)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (KoanaKPaths.Machine.Balanced.foldCharge (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (KoanaKPaths.Machine.Balanced.accumulate (@List.nil.{0} KoanaKPaths.Machine.Balanced.Chunk) xs))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))) (@List.length.{0} Int xs)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int xs))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by sorry
