-- Prove2me | Theorems.Thm_GreedyRS_EFG_lemma7_C_continuous_antitone
-- name    : GreedyRS.EFG.lemma7_C_continuous_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:37.813274+00:00
-- url     : https://prove2.me/theorems/75bf108d-7648-404a-8b4a-01085db953f5
-- title:
--   Lemma 7, p. ec6 — C(x; n₀) = E[Ñ(x; n₀)] is strictly decreasing and continuous on (0, ∞)
-- statement:
--   Let $Z_1, Z_2,\dots$ be iid $N(0,1)$, $\bar Z(n) = \frac1n\sum_{j\le n} Z_j$, and for a positive integer $n_0$ let $N(x; n_0) = \inf\{n \ge n_0 : \bar Z(n) < x\}$. Then
--   $$C(x;n_0) = \mathrm E[N(x;n_0)]$$
--   is a strictly decreasing and continuous function of $x \in (0, \infty)$.
--
--   Together with $C(0; n_0) = \infty$ (Lemma 4), this makes the level $\gamma_0$ in Theorem 3, defined by $C((\gamma-\gamma_0)/\bar\sigma; n_0) = n_g + n_0$, well defined and unique.
--
--   **Formalization Note** $C(\cdot; n_0)$ takes values in $[0,\infty]$; on $(0,\infty)$ the values are finite by Lemma 4, and continuity is with respect to the order topology of $[0,\infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec6, Lemma 7 (EC.2.2)

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem lemma7_C_continuous_antitone (n0 : ℕ) (hn0 : 1 ≤ n0) :
    StrictAntiOn (fun x => GreedyRS.Greedy.Cn0 x n0) (Set.Ioi 0) ∧
    ContinuousOn (fun x => GreedyRS.Greedy.Cn0 x n0) (Set.Ioi 0) := by sorry

end GreedyRS.EFG
