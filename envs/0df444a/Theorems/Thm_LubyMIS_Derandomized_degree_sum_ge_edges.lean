-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_degree_sum_ge_edges
-- name    : LubyMIS.Derandomized.degree_sum_ge_edges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:57:10.576985+00:00
-- url     : https://prove2.me/theorems/48f1251e-299e-41a5-93ee-206a2830c6b6
-- title:
--   Proof of Theorem 1, closing chain — ½ Σ_{sum(i) ≤ 2} d(i)·sum(i) + Σ_{sum(i) > 2} d(i) ≥ |E′|
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph, with degrees $d(i)$ and $\mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} 1/d(j)$. Then
--   $$\frac12 \sum_{i \in V',\ \mathrm{sum}(i) \le 2} d(i)\,\mathrm{sum}(i) \ +\ \sum_{i \in V',\ \mathrm{sum}(i) > 2} d(i) \ \ge\ |E'| .$$
--
--   Multiplied by $\tfrac18$ this is the closing chain of the proof of Theorem 1; it turns the per-vertex bounds $\Pr[i \in N(I')] \ge c \cdot \min\{\mathrm{sum}(i), 1\}$ into a bound proportional to the number of edges. Theorems 2 and 3 use it in place of Theorem 1's Lemma B.
--
--   **Formalization Note** The page's chain carries the common factor $\tfrac18$, divided out here. Vertices of degree $0$ have $\mathrm{sum}(i) = 0$ in Lean and fall in the first sum with weight $0$. The statement is identical to the one in the companion mission on Algorithms A and B.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1041, §3.4, proof of Theorem 1, closing chain

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

namespace LubyMIS.Derandomized

/-- Closing chain of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), with the common factor `⅛`
divided out: `½ ∑_{sum(i) ≤ 2} d(i) sum(i) + ∑_{sum(i) > 2} d(i) ≥ |E′|`. -/
theorem degree_sum_ge_edges {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2), (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) ≥
      (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.Derandomized
