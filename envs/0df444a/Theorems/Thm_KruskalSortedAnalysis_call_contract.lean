-- Prove2me | Theorems.Thm_KruskalSortedAnalysis_call_contract
-- name    : KruskalSortedAnalysis.call_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:55:07.770631+00:00
-- url     : https://prove2.me/theorems/2834173e-3d38-48bf-a47e-16084cc7e06a
-- title:
--   Kruskal after sorting: reusable explicit runtime contract
-- statement:
--   Expose a returning Call, the minimum spanning forest and flag representation, fresh output, unchanged caller storage, actual counter increments, the explicit post-sorting budget and zero sorting increments.
--
--   This result is part of the [Algo2Lean](https://www.algo2lean.com/) formalization of CLRS, fourth edition, Chapter 21, §21.2. It is a supporting reusable contract for the separately stated total and post-sorting runtime theorems. Union-find correctness and inverse-Ackermann amortization are imported from the existing published component, and the full algorithm also imports the existing sorting contract.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/9755b41d188977ae1aafdaf9eccdac0b0edb0420/examples/kruskal/analysis/kruskal_sorted.lean#L162-L184

import Definitions.Def_Algo_kruskal_sorted_Analysis
import Theorems.Thm_KruskalSortedAnalysis_call_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalSortedAnalysis.call_contract :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights order : Algo2LeanGenerated.SeqRef),
      Algo.kruskal_sorted.kruskal_sorted.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources
              (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order))))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
            Exists.{1} fun final =>
              Exists.{1} fun chosen =>
                Exists.{1} fun selected =>
                  Algo.kruskal_sorted.kruskal_sorted.Call heap
                      (Prod.mk.{0, 0} size
                        (Prod.mk.{0, 0} sources
                          (Prod.mk.{0, 0} targets
                            (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order)))))
                      final chosen ∧
                    Algo2Lean.Kruskal.MinimumSpanningForest
                        (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights)
                          count)
                        selected ∧
                      KruskalAnalysis.Flags (final.read chosen) selected ∧
                        heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                          LE.le.{0} heap.nextRef chosen ∧
                            LT.lt.{0} chosen final.nextRef ∧
                              heap.Increments final (heap.cost final) ∧
                                LE.le.{0} (KruskalSortedAnalysis.runtime (heap.cost final))
                                    (KruskalSortedAnalysis.runtimeBound size.toNat count.toNat) ∧
                                  ∀ (clock : String),
                                    ¬Membership.mem.{0, 0}
                                          (List.cons.{0} "uf_init"
                                            (List.cons.{0} "uf_find"
                                              (List.cons.{0} "uf_compress"
                                                (List.cons.{0} "uf_union"
                                                  (List.cons.{0} "kruskal" List.nil.{0})))))
                                          clock →
                                      Eq.{1} (heap.cost final clock) (0 : Nat) := by
  sorry
