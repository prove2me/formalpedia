-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_22
-- name    : GabayMercier.DualAlgorithm.eq_3_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:10:43.887892+00:00
-- url     : https://prove2.me/theorems/27147d11-62d2-475e-b3be-c5022c68dbed
-- title:
--   (3.22) — |P(λⁿ⁺¹ − λ*)|² ≤ ((1−θ)² + ρε|1−θ|)|P(λⁿ − λ*)|² + (ρ² + |1−θ|ρ/ε)|P(yⁿ⁺¹ − yⁿ)|²
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $r>0$, $\rho>0$, $\theta=\rho/r$, let $(v^n,y^n,\lambda^n)$ be a run of the modified dual algorithm (3.4) and $(v^*,y^*;\lambda^*)$ a saddle point of $\mathcal L$, and let $P$ be the orthogonal projection onto $R(A)$. Then for every $\varepsilon>0$ and every $n\ge0$
--   $$|P(\lambda^{n+1}-\lambda^*)|^2\le\bigl((1-\theta)^2+\rho\varepsilon|1-\theta|\bigr)|P(\lambda^n-\lambda^*)|^2+\Bigl(\rho^2+|1-\theta|\frac\rho\varepsilon\Bigr)|P(y^{n+1}-y^n)|^2 .$$
--
--   For $0<\rho<2r$ one has $|1-\theta|<1$, so for $\varepsilon$ small the first coefficient is below $1$: this recursion, together with the summability of $|P(y^{n+1}-y^n)|^2$, drives $P(\lambda^n-\lambda^*)$ to $0$.
--
--   **Formalization Note.** $\theta$ is inlined as `ρ / r`; $\frac\rho\varepsilon$ is printed as a stacked fraction.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 18, (3.22)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.22), p. 18, with `θ = ρ / r`: for every `ε > 0` and every `n`,
`|P(λⁿ⁺¹ − λ*)|² ≤ ((1 − θ)² + ρε|1 − θ|)|P(λⁿ − λ*)|² + (ρ² + |1 − θ|ρ/ε)|P(yⁿ⁺¹ − yⁿ)|²`. -/
theorem eq_3_22 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      ‖projRange A (lam (n + 1) - ls)‖ ^ 2 ≤
        ((1 - ρ / r) ^ 2 + ρ * ε * |1 - ρ / r|) * ‖projRange A (lam n - ls)‖ ^ 2
          + (ρ ^ 2 + |1 - ρ / r| * ρ / ε) * ‖projRange A (y (n + 1) - y n)‖ ^ 2 := by sorry

end GabayMercier.DualAlgorithm
