-- Prove2me | Theorems.Thm_ModernOnlineLearning_ToX_corollary_16_7
-- name    : ModernOnlineLearning.ToX.corollary_16_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:53.501857+00:00
-- url     : https://prove2.me/theorems/761fdc11-2140-45cd-b421-ec1f69df6956
-- title:
--   Corollary 16.7 (Massart's Lemma) — G∞√(2 ln d)/√T
-- statement:
--   Let $d,T\ge1$, let $z_1,\ldots,z_T\in\mathbb R^d$, and assume every coordinate obeys $|z_{t,i}|\le G_\infty$. For the linear class indexed by the probability simplex, the empirical Rademacher complexity equals the average of the largest signed coordinate sum and satisfies
--
--   $$
--   \frac1T\mathbb E_\varepsilon\left[\max_{1\le i\le d}\sum_{t=1}^T\varepsilon_tz_{t,i}\right]
--   \le\frac{G_\infty\sqrt{2\ln d}}{\sqrt T}.
--   $$
--
--   This is the explicit finite-class complexity bound obtained from the online-learning reduction and Exponentiated Gradient.
--
--   **Formalization Note** The expectation is the exact finite average over all $2^T$ sign assignments. The dimension may be one: then both sides are zero. The coordinate bound is the definition of $\|z_t\|_\infty\le G_\infty$; no online algorithm appears in the goal statement.
-- source:
--   Orabona, arXiv:1912.13213v10, Corollary 16.7, p. 273

import Mathlib
import Definitions.Def_ModernOnlineLearning_ToX_Rademacher

namespace ModernOnlineLearning.ToX

/-- Corollary 16.7 (Massart's Lemma), p. 273. The empirical Rademacher
average is the exact finite sign average and the maximum is over all `d`
simplex vertices. -/
theorem corollary_16_7 {d T : ℕ} [NeZero d] (hT : 1 ≤ T)
    (z : ℕ → Fin d → ℝ) (Ginf : ℝ)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d, |z t i| ≤ Ginf) :
    empiricalRadMax (T := T) hT z ≤
      Ginf * Real.sqrt (2 * Real.log (d : ℝ)) / Real.sqrt (T : ℝ) := by sorry

end ModernOnlineLearning.ToX
