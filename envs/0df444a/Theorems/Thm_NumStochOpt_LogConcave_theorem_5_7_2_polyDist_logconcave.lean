-- Prove2me | Theorems.Thm_NumStochOpt_LogConcave_theorem_5_7_2_polyDist_logconcave
-- name    : NumStochOpt.LogConcave.theorem_5_7_2_polyDist_logconcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:15:17.449088+00:00
-- url     : https://prove2.me/theorems/a073601a-0fcb-49d5-831d-320deadfdc55
-- title:
--   Theorem 5.7.2 — the polynomial distribution function is log-concave on the unit cube $(0,1]^n$
-- statement:
--   Let $N \ge 1$, let $c_1, \dots, c_N > 0$, and let $\alpha_{ij} \le 0$ ($i = 1, \dots, N$, $j = 1, \dots, n$) with $\alpha_{i1} + \dots + \alpha_{in} < 0$ for every $i$. Then the polynomial distribution function
--
--   $$
--   F(z_1, \dots, z_n) = \frac{1}{\sum_{i=1}^{N} c_i\, z_1^{\alpha_{i1}} \cdots z_n^{\alpha_{in}}}
--   $$
--
--   of (5.19) is logarithmically concave on the unit cube $C = \{z : 0 < z_1, \dots, z_n \le 1\}$: for all $z, w \in C$ and $0 < \lambda < 1$,
--
--   $$
--   F(\lambda z + (1-\lambda) w) \ge F(z)^{\lambda} F(w)^{1-\lambda}.
--   $$
--
--   Consequently the set of $z \in C$ with $F(z) \ge p$, for a fixed probability $0 < p < 1$, is convex, which is what makes probabilistic constraints of the form (5.26) tractable.
--
--   **Formalization Note** Points are `Fin n → ℝ`, powers are `Real.rpow`, and log-concavity is the platform predicate `ConvexOptimization.LogConcaveOn` on the half-open cube. The conditions $c_i > 0$, $\alpha_{ij} \le 0$ and $\sum_j \alpha_{ij} < 0$ are the standing conditions of (5.19); the last one forces $n \ge 1$ (for $n = 0$ the hypotheses cannot hold), which matches the book's setting. $N \ge 1$ is assumed so that the sum in the denominator is not empty.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, §5.7, p. 135, Theorem 5.7.2 (definition (5.19) on p. 133)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_NumStochOpt_LogConcave_polyDistF

namespace NumStochOpt.LogConcave

theorem theorem_5_7_2_polyDist_logconcave {N n : ℕ} (hN : 0 < N)
    (c : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (α : Fin N → Fin n → ℝ) (hα : ∀ i j, α i j ≤ 0) (hα_sum : ∀ i, ∑ j, α i j < 0) :
    ConvexOptimization.LogConcaveOn {z : Fin n → ℝ | ∀ j, 0 < z j ∧ z j ≤ 1}
      (polyDistF c α) := by sorry

end NumStochOpt.LogConcave
