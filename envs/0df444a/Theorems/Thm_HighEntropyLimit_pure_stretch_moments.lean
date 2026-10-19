-- Prove2me | Theorems.Thm_HighEntropyLimit_pure_stretch_moments
-- name    : HighEntropyLimit.pure_stretch_moments
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:59:11.052334+00:00
-- url     : https://prove2.me/theorems/62f6bc37-95ae-4160-9b5a-60edb3de4137
-- title:
--   Moments scale under the pure stretching map
-- statement:
--   Let $\lambda > 1$, let $\rho$ be a function on phase space $\mathbb R^2$, and let $T\rho(z) = \lambda^{-1}\rho(z/\sqrt\lambda)$. For all $n,m\in\mathbb N$,
--   $$\int x^n p^m\,(T\rho)(x,p)\,dx\,dp = (\sqrt\lambda)^{n+m}\int x^n p^m\,\rho(x,p)\,dx\,dp.$$
--
--   **Formalization Note** No integrability is assumed. If one side does not converge, neither does the other, and Lean assigns both the value $0$.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 8, Eq. (18)

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch
open MeasureTheory

namespace HighEntropyLimit
theorem pure_stretch_moments (lam : ℝ) (hlam : 1 < lam) (ρ : ℝ × ℝ → ℝ) (n m : ℕ) :
    ∫ z, z.1 ^ n * z.2 ^ m * pureStretch lam ρ z =
      Real.sqrt lam ^ (n + m) * ∫ z, z.1 ^ n * z.2 ^ m * ρ z := by sorry
end HighEntropyLimit
