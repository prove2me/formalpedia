-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_19
-- name    : GabayMercier.DualAlgorithm.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:10:00.442394+00:00
-- url     : https://prove2.me/theorems/bc23d4f9-b0fb-46c6-b481-4c30ee58f77a
-- title:
--   (3.19) — the one-step energy estimate of the modified dual algorithm
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5) with strong-monotonicity constant $\gamma$, let $r>0$, $\rho>0$, let $(v^n,y^n,\lambda^n)$ be a run of the modified dual algorithm (3.4) and $(v^*,y^*;\lambda^*)$ a saddle point of $\mathcal L$. Let $P$ be the orthogonal projection onto $R(A)$ and $I$ the identity of $Y$. Then for every $n\ge0$
--   $$\gamma|y^{n+1}-y^*|^2+\Bigl(r-\frac\rho2\Bigr)|(I-P)(y^{n+1}-y^*)|^2+\frac r2|P(y^{n+1}-y^*)|^2+\frac1{2\rho}|(I-P)(\lambda^{n+1}-\lambda^*)|^2\le\frac r2|P(y^n-y^*)|^2+\frac1{2\rho}|(I-P)(\lambda^n-\lambda^*)|^2 .$$
--
--   This is the central estimate of the convergence proof: the quantity $\frac r2|P(y^n-y^*)|^2+\frac1{2\rho}|(I-P)(\lambda^n-\lambda^*)|^2$ does not increase, and its decrease controls $\gamma|y^{n+1}-y^*|^2$.
--
--   **Formalization Note.** $\frac1{2\rho}$ is printed as a stacked fraction $\frac{1}{2\rho}$. $I-P$ is `ContinuousLinearMap.id ℝ Y - projRange A`. The estimate holds for every $\rho>0$; the coefficient $r-\rho/2$ is non-negative exactly when $\rho\le2r$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 17, (3.19)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.19), p. 17: the one-step energy estimate, with `P` the projection onto `R(A)` and
`I − P` its complement. -/
theorem eq_3_19 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ n : ℕ,
      γ * ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + r / 2 * ‖projRange A (y (n + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (n + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y n - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam n - ls)‖ ^ 2 := by sorry

end GabayMercier.DualAlgorithm
