-- Prove2me | Theorems.Thm_KruskalAnalysis_running_time
-- name    : KruskalAnalysis.running_time
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:06:44.181953+00:00
-- url     : https://prove2.me/theorems/68cf212e-4a7a-4834-8ee7-d0893e01db88
-- title:
--   Kruskal: inverse-Ackermann running time of every returned execution
-- statement:
--   For well-formed finite endpoint data, every `kruskal.ReturnsWithCost` witness with clock increment function `costs` satisfies
--   $$
--   \operatorname{KruskalAnalysis.runtime}(costs)\le B(V,E).
--   $$
--   Here $V$ and $E$ are the nonnegative vertex and edge counts. The weights may be arbitrary integers. This is a finite inequality for any completed execution; existence and the reusable heap/storage contract are established by `call_contract`.
--
--   For $V$ vertices and $E$ edges, define
--   $$
--   B(V,E)=2E\bigl(3\lfloor\log_2(E+1)\rfloor+2\bigr)+V+2+E\bigl(10\alpha(V)+14\bigr).
--   $$
--   The eight unit-weight clocks are `sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`, `uf_compress`, `uf_union`, and `kruskal`. Their sum is `KruskalAnalysis.runtime`; the displayed expression is `KruskalAnalysis.runtimeBound`. Thus the finite inequality has scale $O(V+E\log(E+1)+E\alpha(V))$. The inverse-Ackermann improvement is in the disjoint-set term; sorting still costs $O(E\log(E+1))$.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   Part of the [Algo2Lean](https://www.algo2lean.com/) CLRS series: *Introduction to Algorithms*, fourth edition, Chapter 21, §21.2 (Kruskal), the safe-edge principle in Theorem 21.1 (§21.1), and the union-by-rank/path-compression bound in Theorem 19.14 (§19.4).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal.lean#L264-L271

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_call_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.running_time :
    ∀ {size count : Int} {sources targets weights chosen : Algo2LeanGenerated.Seq}
      {costs : Algo2LeanGenerated.Clocks},
      KruskalInput.WellFormed size count sources targets →
        Algo.kruskal.kruskal.ReturnsWithCost
            (Prod.mk.{0, 0} size
              (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
            chosen costs →
          LE.le.{0} (KruskalAnalysis.runtime costs)
            (KruskalAnalysis.runtimeBound size.toNat count.toNat) := by
  sorry
