-- Prove2me | Theorems.Thm_KruskalAnalysis_call_complete
-- name    : KruskalAnalysis.call_complete
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:04:43.642367+00:00
-- url     : https://prove2.me/theorems/a02075e3-95ba-46a9-af66-437fbaf1f28d
-- title:
--   Kruskal: termination, correctness and inverse-Ackermann running time
-- statement:
--   Let the initial heap contain allocated source, target and weight sequences for a graph with $V\ge0$ vertices and $E\ge0$ edges. Each edge endpoint must lie in $[0,V)$; integer weights are unrestricted and the three sequences may alias. A terminating `kruskal.Call` returns a fresh valid flag sequence describing a minimum spanning forest, preserves all previously allocated caller storage, and satisfies
--   $$
--   \operatorname{runtime}(clocks_{after})\le\operatorname{runtime}(clocks_{before})+B(V,E).
--   $$
--   The final heap, flags, selected-edge list and bound belong to the same call. `call_contract` restates this result directly in terms of clock increments for subsequent callers.
--
--   For $V$ vertices and $E$ edges, define
--   $$
--   B(V,E)=2E\bigl(3\lfloor\log_2(E+1)\rfloor+2\bigr)+V+2+E\bigl(10\alpha(V)+14\bigr).
--   $$
--   The eight unit-weight clocks are `sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`, `uf_compress`, `uf_union`, and `kruskal`. Their sum is `KruskalAnalysis.runtime`; the displayed expression is `KruskalAnalysis.runtimeBound`. Thus the finite inequality has scale $O(V+E\log(E+1)+E\alpha(V))$. The inverse-Ackermann improvement is in the disjoint-set term; sorting still costs $O(E\log(E+1))$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   Part of the [Algo2Lean](https://www.algo2lean.com/) CLRS series: *Introduction to Algorithms*, fourth edition, Chapter 21, §21.2 (Kruskal), the safe-edge principle in Theorem 21.1 (§21.1), and the union-by-rank/path-compression bound in Theorem 19.14 (§19.4).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal.lean#L98-L162

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_scan_contract
import Theorems.Thm_SortIndicesAnalysis_call
import Theorems.Thm_UnionFindAnalysis_constructor_summary
import Theorems.Thm_UnionFindAnalysis_constructor_rep
import Theorems.Thm_Algo2Lean_Kruskal_Scan_minimum_spanning_forest

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.call_complete :
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
                      LE.le.{0} (KruskalAnalysis.runtime final.clocks)
                          (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.runtime heap.clocks)
                            (KruskalAnalysis.runtimeBound size.toNat count.toNat)) ∧
                        heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                          LE.le.{0} heap.nextRef chosen ∧ LT.lt.{0} chosen final.nextRef := by
  sorry
