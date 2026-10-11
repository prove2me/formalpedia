-- Prove2me | Theorems.Thm_KruskalAnalysis_edge_contract
-- name    : KruskalAnalysis.edge_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:02:03.639166+00:00
-- url     : https://prove2.me/theorems/5d698756-7a86-4da2-8781-89116504b395
-- title:
--   Kruskal edge selection and inverse-Ackermann running time
-- statement:
--   This is the reusable proof step for one edge in textbook MST-KRUSKAL (CLRS fourth edition, Section 21.2). Assume `ScanInvariant` at an edge-loop boundary: the union-find partition agrees with the already selected edges, the flags record exactly those edges, the next edge has valid endpoints, and the private arrays are separated from the input and order arrays.
--
--   The theorem produces an updated heap and union-find model, together with an `accepted` Boolean. Acceptance is equivalent to the endpoints being disconnected by the previously selected edges. `EdgeCalls` records two actual full-compression finds and, only in the accepted case, a selection write followed by an actual union. The resulting `ScanInvariant` advances the edge index by one and adds the edge exactly when accepted. No storage outside the parent, rank, and selection arrays changes; clocks outside the scan and union-find operations also remain unchanged.
--
--   For `n` vertices, the scan/union-find work increases by at most `8 log₂(n) + 6`. The sharper amortized statement is
--
--   ```text
--   work(after) + 2 Φ(nextModel)
--     ≤ work(before) + 2 Φ(model) + 10 α(n) + 14.
--   ```
--
--   Here `α` is `Algo2Lean.Ackermann.alpha`, `Φ` is the independently proved union-find potential, and `work` sums the named union-find and Kruskal clocks. These are inequalities for the same actual before/after heap and model. Summing this contract over the edge loop cancels intermediate potentials; it does not charge a fresh data structure for each edge. The surrounding source-transition lemma and `scan_contract` connect these recorded operation calls to the compiled `kruskal.CallFrom` loop.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal_scan.lean#L365-L476

import Definitions.Def_Algo_kruskal_scan_Analysis
import Theorems.Thm_UnionFindAnalysis_find_contract
import Theorems.Thm_UnionFindAnalysis_union_summary_amortized
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.edge_contract :
    ∀ {n : Nat} (data : KruskalAnalysis.ScanLayout) (heap : Algo2LeanGenerated.Heap)
      (model : Algo2Lean.UnionFind.State n) (index : Int) (edge : Algo2Lean.Kruskal.Edge)
      (pending selected : List.{0} Algo2Lean.Kruskal.Edge),
      KruskalAnalysis.ScanInvariant n data heap model index (List.cons.{0} edge pending) selected →
        Exists.{1} fun after =>
          Exists.{1} fun nextModel =>
            Exists.{1} fun accepted =>
              (Eq.{1} accepted Bool.true ↔
                  ¬Algo2Lean.Kruskal.Connected selected edge.source edge.target) ∧
                KruskalAnalysis.EdgeCalls data heap after (↑edge.id : Int) edge.source edge.target ∧
                  KruskalAnalysis.ScanInvariant n data after nextModel
                      (HAdd.hAdd.{0, 0, 0} index (1 : Int)) pending
                      (ite.{1} (Eq.{1} accepted Bool.true) (List.cons.{0} edge selected) selected) ∧
                    heap.Footprint after
                        (List.cons.{0} data.sets.parent
                          (List.cons.{0} data.sets.rank (List.cons.{0} data.chosen List.nil.{0})))
                        List.nil.{0} List.nil.{0} ∧
                      (∀ (clock : String),
                          ¬Membership.mem.{0, 0}
                                (List.cons.{0} "kruskal"
                                  (List.cons.{0} "uf_find"
                                    (List.cons.{0} "uf_compress"
                                      (List.cons.{0} "uf_union" List.nil.{0}))))
                                clock →
                            Eq.{1} (after.clocks clock) (heap.clocks clock)) ∧
                        LE.le.{0} (KruskalAnalysis.work after.clocks)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                (HMul.hMul.{0, 0, 0} (8 : Nat) n.log2))
                              (6 : Nat)) ∧
                          LE.le.{0}
                            (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work after.clocks)
                              (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential nextModel)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model)))
                                (HMul.hMul.{0, 0, 0} (10 : Nat) (Algo2Lean.Ackermann.alpha n)))
                              (14 : Nat)) := by
  sorry
