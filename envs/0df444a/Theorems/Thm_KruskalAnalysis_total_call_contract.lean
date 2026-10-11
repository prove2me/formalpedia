-- Prove2me | Theorems.Thm_KruskalAnalysis_total_call_contract
-- name    : KruskalAnalysis.total_call_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:55:30.417891+00:00
-- url     : https://prove2.me/theorems/c614c06c-567e-4c80-a548-b08913ff1c8f
-- title:
--   Kruskal: reusable explicit runtime contract including sorting
-- statement:
--   Compose the existing sorting contract with the shared post-sorting proof; retain minimum spanning forest correctness, actual counter increments, fresh output, caller preservation and the explicit total budget.
--
--   This result is part of the [Algo2Lean](https://www.algo2lean.com/) formalization of CLRS, fourth edition, Chapter 21, §21.2. It is a supporting reusable contract for the separately stated total and post-sorting runtime theorems. Union-find correctness and inverse-Ackermann amortization are imported from the existing published component, and the full algorithm also imports the existing sorting contract.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/9755b41d188977ae1aafdaf9eccdac0b0edb0420/examples/kruskal/analysis/kruskal.lean#L174-L186

import Definitions.Def_Algo_kruskal_Analysis_SortedRevision
import Theorems.Thm_KruskalSortedAnalysis_call_complete
import Theorems.Thm_SortIndicesAnalysis_call

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.total_call_contract :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights : Algo2LeanGenerated.SeqRef),
      Algo.kruskal.kruskal.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          Exists.{1} fun final =>
            Exists.{1} fun chosen =>
              Exists.{1} fun selected =>
                Algo.kruskal.kruskal.Call heap
                    (Prod.mk.{0, 0} size
                      (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
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
                              LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                (KruskalAnalysis.runtimeBound size.toNat count.toNat) := by
  sorry
