-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_y_tendsto
-- name    : GabayMercier.DualAlgorithm.y_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:10:46.136986+00:00
-- url     : https://prove2.me/theorems/5ddba732-396a-4b4c-ac39-16577515ca85
-- title:
--   p. 17, after (3.20) — for 0 < ρ ≤ 2r, yⁿ → y* strongly in Y
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $r>0$ and $0<\rho\le2r$, let $(v^n,y^n,\lambda^n)$ be a run of the modified dual algorithm (3.4) and $(v^*,y^*;\lambda^*)$ a saddle point of $\mathcal L$. Then
--   $$\lim_{n\to\infty}|y^n-y^*|=0 ,$$
--   i.e. $y^n\to y^*$ in the norm topology of $Y$.
--
--   Since $y^*=Av^*$ for a saddle point, this is the $y$-half of Theorem 3.1, and it holds on the closed range $0<\rho\le2r$.
--
--   **Formalization Note.** Strong convergence is convergence in norm (`Tendsto y atTop (𝓝 ys)`). The paper's step "the series remains bounded and so, convergent" is a step of the proof, not part of the statement.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 17, after (3.20)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- p. 17, after (3.20): for `0 < ρ ≤ 2r`, `yⁿ → y*` strongly in `Y`. -/
theorem y_tendsto (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) (hρr : ρ ≤ 2 * r) :
    Tendsto y atTop (𝓝 ys) := by sorry

end GabayMercier.DualAlgorithm
