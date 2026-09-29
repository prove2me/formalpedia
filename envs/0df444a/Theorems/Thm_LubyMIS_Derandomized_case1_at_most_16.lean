-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_case1_at_most_16
-- name    : LubyMIS.Derandomized.case1_at_most_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:00:25.466066+00:00
-- url     : https://prove2.me/theorems/7ff609b9-5729-4b1f-8a82-878c2dcf221c
-- title:
--   Case 1 occurs at most 16 times in a run of Algorithm D
-- statement:
--   Let $G$ be a graph on the vertices $\{0, \dots, n-1\}$ and $q$ a prime with $n \le q \le 2n$. In every run of Algorithm D, at most $16$ executions of the loop body are in Case 1, that is, begin (after the deletion of isolated vertices) with a vertex of degree $d(i) \ge n/16$ in the current graph:
--   $$\bigl|\{ k < K : V'_j \ne \emptyset \text{ for all } j \le k, \text{ and state } k \text{ is in Case 1} \}\bigr| \ \le\ 16 \qquad \text{for every } K .$$
--
--   Each Case 1 round deletes a vertex together with at least $n/16$ neighbours, that is, at least $1/16$ of the vertices of the original graph.
--
--   **Formalization Note** $n$ is the number of vertices of the input graph $G$, not of the current graph. The bound is stated for every finite prefix of the run. Only executions before termination are counted ($V'_j \ne \emptyset$ for every $j \le k$): after the first index with $V' = \emptyset$ the run relation leaves the sequence unconstrained, so a later state could restart the algorithm.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1046, §4.4 ("Case 1 can occur at most 16 times")

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

namespace LubyMIS.Derandomized

/-- Case 1 is rare (Luby 1986, §4.4, p. 1046): in every run of Algorithm D, Case 1 occurs in at most
16 executions of the loop body. Only the executions before termination are counted (`V′` nonempty at
every index up to `k`): after the first index with `V′ = ∅` a run is unconstrained. -/
theorem case1_at_most_16 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) (K : ℕ) :
    ((Finset.range K).filter
      (fun k => (∀ j ≤ k, (s j).2.Nonempty) ∧ Case1 G (s k))).card ≤ 16 := by sorry

end LubyMIS.Derandomized
