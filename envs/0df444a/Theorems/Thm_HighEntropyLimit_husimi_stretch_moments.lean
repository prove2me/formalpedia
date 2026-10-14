-- Prove2me | Theorems.Thm_HighEntropyLimit_husimi_stretch_moments
-- name    : HighEntropyLimit.husimi_stretch_moments
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:59:54.544661+00:00
-- url     : https://prove2.me/theorems/9202d617-b9ab-49bc-ac6d-cf84319e2910
-- title:
--   Anti-normally ordered moments scale under the Husimi stretch
-- statement:
--   Let $\lambda>1$, let $Q_1:\mathbb C\to\mathbb R$, and let $Q_\lambda(\alpha) = \lambda^{-1}Q_1(\alpha/\sqrt\lambda)$. For all $n,m\in\mathbb N$,
--   $$\int_{\mathbb C}\alpha^n(\alpha^*)^m\,Q_\lambda(\alpha)\,d^2\alpha = (\sqrt\lambda)^{n+m}\int_{\mathbb C}\beta^n(\beta^*)^m\,Q_1(\beta)\,d^2\beta.$$
--
--   Through Eq. (23) this says that the stretch rescales every anti-normally ordered moment $\langle a^n(a^\dagger)^m\rangle$ by $(\sqrt\lambda)^{n+m}$.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 9, Eqs. (24),(25)

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch
open MeasureTheory ComplexConjugate

namespace HighEntropyLimit
theorem husimi_stretch_moments (lam : ℝ) (hlam : 1 < lam) (Q : ℂ → ℝ) (n m : ℕ) :
    ∫ α : ℂ, α ^ n * (conj α) ^ m * (husimiStretch lam Q α : ℂ) =
      ((Real.sqrt lam : ℝ) : ℂ) ^ (n + m) * ∫ β : ℂ, β ^ n * (conj β) ^ m * (Q β : ℂ) := by
  sorry
end HighEntropyLimit
