-- Prove2me | Theorems.Thm_GreedyRS_EFG_lemma4_crossing_time
-- name    : GreedyRS.EFG.lemma4_crossing_time
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:42.736013+00:00
-- url     : https://prove2.me/theorems/6658e860-708a-4cf7-820b-fe8ea4884a70
-- title:
--   Lemma 4, p. 22 — finiteness and mean of the crossing time Ñ(x; n₀) for x > 0, x < 0 and x = 0
-- statement:
--   Let $Z_1, Z_2, \dots$ be iid $N(0,1)$, $\bar Z(n) = \frac1n \sum_{j \le n} Z_j$, and $\tilde N(x; n_0) = \inf\{n \ge n_0 : \bar Z(n) < x\}$ (with $\inf\emptyset = \infty$). For every positive integer $n_0$:
--
--   1. for any $x > 0$: $\Pr\{\tilde N(x;n_0) < \infty\} = 1$ and $\mathrm E[\tilde N(x;n_0)] < \infty$;
--   2. for any $x < 0$: $0 < \Pr\{\tilde N(x;n_0) < \infty\} < 1$ and $\mathrm E[\tilde N(x;n_0)] = \infty$;
--   3. for $x = 0$: $\Pr\{\tilde N(0;n_0) < \infty\} = 1$ and $\mathrm E[\tilde N(0;n_0)] = \infty$.
--
--   In particular $C(x; n_0) = \mathrm E[\tilde N(x;n_0)]$ is finite exactly for $x > 0$, which is where the budget conditions of Theorems 3 and 4 evaluate it.
--
--   **Formalization Note** The expectation is the integral of an $\mathbb N\cup\{\infty\}$-valued variable in $[0,\infty]$, so "$=\infty$" is literal.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 22, Lemma 4

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem lemma4_crossing_time (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (∀ x : ℝ, 0 < x →
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 x n0 < ⊤) ∧
    (∀ x : ℝ, x < 0 →
      0 < GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} ∧
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} < 1 ∧ GreedyRS.Greedy.Cn0 x n0 = ⊤) ∧
    (GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime 0 n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 0 n0 = ⊤) := by sorry

end GreedyRS.EFG
