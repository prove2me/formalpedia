-- Prove2me | Theorems.Thm_KruskalAnalysis_scan_contract
-- name    : KruskalAnalysis.scan_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:03:17.348983+00:00
-- url     : https://prove2.me/theorems/883a9adf-586f-474f-95e3-eaadb771ce30
-- title:
--   Kruskal scan: correctness and inverse-Ackermann running time
-- statement:
--   The scan invariant connects allocated endpoint, order and flag arrays, a represented union-find partition, and the pending and selected edges. From the named loop boundary of `kruskal`, the `CallFrom` contract supplies a terminating continuation returning the same flag reference and an abstract `Scan` with the final invariant.
--
--   Only the private parent, rank and chosen arrays may change. For m pending edges, the actual work and the same evolving union-find potential satisfy
--
--   $$W_{after}+2\Phi(S_{after})\le W_{before}+2\Phi(S_{before})+m(10\alpha(n)+14).$$
--
--   Here W sums the four union-find clocks and `kruskal`. Each edge adds one scan tick and two explicit find calls; accepted edges also invoke union, including its internal finds. Sortedness is not required for this operational scan theorem. Minimum spanning forest correctness follows separately from sorted input and the graph exchange theorem.
--
--   The bound measures named tick increments from arbitrary initial counters, not wall-clock time or every primitive operation.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal_scan.lean#L477-L536

import Definitions.Def_Algo_kruskal_scan_Analysis
import Theorems.Thm_KruskalAnalysis_edge_contract

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.scan_contract :
    ∀ {n : Nat} (data : KruskalAnalysis.ScanLayout) (heap : Algo2LeanGenerated.Heap)
      (model : Algo2Lean.UnionFind.State n) (index count : Int)
      (pending selected : List.{0} Algo2Lean.Kruskal.Edge),
      KruskalAnalysis.ScanInvariant n data heap model index pending selected →
        Eq.{1} (HAdd.hAdd.{0, 0, 0} index (↑(List.length.{0} pending) : Int)) count →
          Exists.{1} fun final =>
            Exists.{1} fun nextModel =>
              Exists.{1} fun result =>
                KruskalAnalysis.ScanCall data heap index count final ∧
                  KruskalAnalysis.ScanInvariant n data final nextModel count List.nil.{0} result ∧
                    Algo2Lean.Kruskal.Scan pending selected result ∧
                      heap.Footprint final
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
                              Eq.{1} (final.clocks clock) (heap.clocks clock)) ∧
                          LE.le.{0} (KruskalAnalysis.work final.clocks)
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                (HMul.hMul.{0, 0, 0} (List.length.{0} pending)
                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Nat) n.log2)
                                    (6 : Nat)))) ∧
                            LE.le.{0}
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work final.clocks)
                                (HMul.hMul.{0, 0, 0} (2 : Nat)
                                  (Algo2Lean.UnionFind.potential nextModel)))
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model)))
                                (HMul.hMul.{0, 0, 0} (List.length.{0} pending)
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (10 : Nat) (Algo2Lean.Ackermann.alpha n))
                                    (14 : Nat)))) := by
  sorry
