-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_theorem_3_4_i
-- name    : NonconvexDRS.DRS.theorem_3_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:55.631865+00:00
-- url     : https://prove2.me/theorems/5db408ec-5af2-4d8f-8db2-073bfdc9f1fb
-- title:
--   Theorem 3.4(i), p. 9 — under Assumption I and γ < 1/L, inf φ = inf φ^DR_γ
-- statement:
--   Suppose Assumption I holds ($\varphi_1$ $L$-smooth and $\sigma$-hypoconvex with $\sigma\in[-L,L]$, $\varphi_2$ proper lsc, $\operatorname{arg\,min}\varphi\ne\emptyset$). For every $0<\gamma<1/L$,
--   $$\inf_{x\in\mathbb R^p}\varphi(x)=\inf_{s\in\mathbb R^p}\varphi^{\mathrm{DR}}_\gamma(s).$$
--
--   The envelope therefore has the same optimal value as the original problem, so the telescoped decrease of $\varphi^{\mathrm{DR}}_\gamma$ along DRS is bounded by $\varphi^{\mathrm{DR}}_\gamma(s^0)-\inf\varphi$.
--
--   **Formalization Note** Both infima are taken in `EReal`. $L>0$ is the mission's standing addition; $\gamma<1/L$ is $\gamma L<1$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 9, Theorem 3.4(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Theorem 3.4 (i), p. 9: `inf φ = inf φ^DR_γ`. -/
theorem theorem_3_4_i {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * L < 1) :
    ⨅ x, phi φ₁ φ₂ x = ⨅ s, dre φ₁ φ₂ γ s := by sorry

end NonconvexDRS.DRS
