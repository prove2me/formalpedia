-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_P_lam_tendsto_and_v_tendsto
-- name    : GabayMercier.DualAlgorithm.P_lam_tendsto_and_v_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:13:33.950745+00:00
-- url     : https://prove2.me/theorems/1e587025-1ae9-46f2-8cf7-50f99971b11d
-- title:
--   p. 18, after (3.24) — for 0 < ρ < 2r, P(λⁿ − λ*) → 0 and vⁿ → v* strongly in V
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $r>0$ and $0<\rho<2r$, let $(v^n,y^n,\lambda^n)$ be a run of the modified dual algorithm (3.4) and $(v^*,y^*;\lambda^*)$ a saddle point of $\mathcal L$, and let $P$ be the orthogonal projection onto $R(A)$. Then
--   $$|P(\lambda^n-\lambda^*)|\to0\qquad\text{and}\qquad\|v^n-v^*\|\to0 .$$
--
--   Together with $y^n\to y^*=Av^*$ and the boundedness of $(I-P)(\lambda^n-\lambda^*)$ from (3.20), this gives Theorem 3.1. The strict bound $\rho<2r$ is needed here.
--
--   **Formalization Note.** Both limits are in norm. The step "$|A(v^{n+1}-v^*)|\to0$" of the paper is part of the proof, not of the statement.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 18, after (3.24)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- p. 18, after (3.24): for `0 < ρ < 2r`, `P(λⁿ − λ*) → 0` and `vⁿ → v*` strongly in `V`. -/
theorem P_lam_tendsto_and_v_tendsto (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) (hρr : ρ < 2 * r) :
    Tendsto (fun n => projRange A (lam n - ls)) atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 vs) := by sorry

end GabayMercier.DualAlgorithm
