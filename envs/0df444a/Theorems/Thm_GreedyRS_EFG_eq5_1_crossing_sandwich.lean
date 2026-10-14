-- Prove2me | Theorems.Thm_GreedyRS_EFG_eq5_1_crossing_sandwich
-- name    : GreedyRS.EFG.eq5_1_crossing_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:34.273581+00:00
-- url     : https://prove2.me/theorems/8c113ded-e92b-47c4-bd85-d552a9d01ccb
-- title:
--   (5.1), p. 22 — Ñ(x) ≤ Ñ(x; n₀) ≤ n₀·inf{m ≥ 1 : Z̄(mn₀) < x}, the latter distributed as Ñ(√n₀·x)
-- statement:
--   Let $Z_1, Z_2, \dots$ be iid $N(0,1)$, $\bar Z(n) = \frac1n\sum_{j\le n} Z_j$, $\tilde N(x;n_0) = \inf\{n\ge n_0 : \bar Z(n) < x\}$ and $\tilde N(x) = \tilde N(x;1)$. For every integer $n_0 \ge 1$ and every real $x$:
--
--   1. pathwise, $\tilde N(x) \le \tilde N(x; n_0)$;
--   2. pathwise, $\tilde N(x; n_0) \le n_0 \inf\{m \ge 1 : \bar Z(m n_0) < x\}$;
--   3. the block crossing time $\inf\{m \ge 1 : \bar Z(m n_0) < x\}$ has the same distribution as $\tilde N(\sqrt{n_0}\, x)$.
--
--   Together,
--   $$\tilde N(x) \le \tilde N(x; n_0) \le_{\mathrm{st}} n_0\, \tilde N\big(\sqrt{n_0}\,x\big).$$
--
--   This sandwich transfers the finiteness and infiniteness properties of the $n_0 = 1$ crossing time to $\tilde N(x; n_0)$ (Lemma 4).
--
--   **Formalization Note** The paper prints the right-hand end as $n_0\tilde N(x/\sqrt{n_0})$, from "$\bar Z(mn_0) = \sqrt{n_0}\,\bar Z(m)$ statistically". The correct scaling is $\bar Z(mn_0) \overset{d}{=} \bar Z(m)/\sqrt{n_0}$ (the $n_0$-blocks sum to $\sqrt{n_0}$ times iid standard normals), so the block crossing time has the law of $\tilde N(\sqrt{n_0}\,x)$; this is stated here. For $x > 0$ the printed bound is a weaker consequence; for $x < 0$ and $n_0 \ge 2$ it is false. Equality in distribution is stated as equality of the probabilities of every preimage, and all crossing times take values in $\mathbb N\cup\{\infty\}$ (infimum of the empty set $= \infty$).
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 22, display before (5.1) and Equation (5.1) (scaling corrected)

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem eq5_1_crossing_sandwich (n0 : ℕ) (hn0 : 1 ≤ n0) (x : ℝ) :
    (∀ z, GreedyRS.Greedy.crossTime x 1 z ≤ GreedyRS.Greedy.crossTime x n0 z) ∧
    (∀ z, GreedyRS.Greedy.crossTime x n0 z ≤ (n0 : ℕ∞) * blockCross x n0 z) ∧
    (∀ s : Set ℕ∞, GreedyRS.Greedy.stdNormalSeq (blockCross x n0 ⁻¹' s) =
      GreedyRS.Greedy.stdNormalSeq (GreedyRS.Greedy.crossTime (Real.sqrt n0 * x) 1 ⁻¹' s)) := by sorry

end GreedyRS.EFG
