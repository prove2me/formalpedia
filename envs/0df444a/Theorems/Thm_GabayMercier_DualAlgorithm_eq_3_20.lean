-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_20
-- name    : GabayMercier.DualAlgorithm.eq_3_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:10:35.952601+00:00
-- url     : https://prove2.me/theorems/2618e210-a56e-4306-ae6c-80c92c7dbc5b
-- title:
--   (3.20) — the summed energy estimate over n = 0, …, N
-- statement:
--   In the setting of (3.19) ($r>0$, $\rho>0$, a run of (3.4), a saddle point $(v^*,y^*;\lambda^*)$ of $\mathcal L$), for every $N\ge0$
--   $$\gamma\sum_{n=0}^{N}|y^{n+1}-y^*|^2+\Bigl(r-\frac\rho2\Bigr)\sum_{n=0}^{N}|(I-P)(y^{n+1}-y^*)|^2+\frac1{2\rho}|(I-P)(\lambda^{N+1}-\lambda^*)|^2\le\frac r2|P(y^0-y^*)|^2+\frac1{2\rho}|(I-P)(\lambda^0-\lambda^*)|^2 .$$
--
--   For $0<\rho\le2r$ every term on the left is non-negative, so the partial sums $\sum|y^{n+1}-y^*|^2$ and the multiplier components $(I-P)(\lambda^n-\lambda^*)$ are bounded independently of $N$.
--
--   **Formalization Note.** The left-hand side is exactly the printed one: the term $\frac r2|P(y^{N+1}-y^*)|^2$, which the summation also produces, is dropped as in the paper. The inequality holds for every $\rho>0$; the paper uses it for $0<\rho\le2r$ (p. 17), where it gives boundedness.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 17, (3.20)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.20), p. 17: (3.19) summed over `n = 0, …, N`. -/
theorem eq_3_20 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ N : ℕ,
      γ * ∑ n ∈ Finset.range (N + 1), ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ∑ n ∈ Finset.range (N + 1),
            ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (N + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y 0 - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam 0 - ls)‖ ^ 2 := by sorry

end GabayMercier.DualAlgorithm
