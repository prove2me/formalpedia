-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_degree_sum_ge_edges
-- name    : LubyMIS.MonteCarlo.degree_sum_ge_edges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:52:46.503986+00:00
-- url     : https://prove2.me/theorems/3aa692aa-d655-4338-8d61-335d0333737d
-- title:
--   Proof of Theorem 1, closing chain — ½·Σ_{sum(i)≤2} d(i)·sum(i) + Σ_{sum(i)>2} d(i) ≥ |E′|
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph with degrees $d(i)$, and let $\mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} 1/d(j)$ (the empty sum $0$ for an isolated vertex). Then
--   $$\frac12 \sum_{\substack{i \in V' \\ \mathrm{sum}(i) \le 2}} d(i)\, \mathrm{sum}(i) \;+\; \sum_{\substack{i \in V' \\ \mathrm{sum}(i) > 2}} d(i) \;\ge\; |E'| .$$
--
--   This is the purely graph-theoretic closing chain of the proof of Theorem 1. Combined with the first display of that proof and Lemma B, which give $E[Y_k - Y_{k+1}] \ge \frac18$ times the left-hand side, it yields $E[Y_k^B - Y_{k+1}^B] \ge \frac18 |E'|$.
--
--   **Formalization Note** The page writes the chain with the common factor $\frac18$ in front of every line; the statement divides it out. Isolated vertices have $\mathrm{sum}(i) = 0$ and degree $0$, so they fall in the first sum with weight $0$, matching the page, where they carry no edges.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1041, §3.4, proof of Theorem 1, closing chain of displays

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- Closing chain of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), with the common factor `⅛`
divided out: `½ ∑_{sum(i) ≤ 2} d(i) sum(i) + ∑_{sum(i) > 2} d(i) ≥ |E′|`. -/
theorem degree_sum_ge_edges {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2), (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) ≥
      (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.MonteCarlo
