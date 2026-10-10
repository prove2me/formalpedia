-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_theorem_3_4_iii
-- name    : NonconvexDRS.DRS.theorem_3_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:48.86098+00:00
-- url     : https://prove2.me/theorems/df4bb3f5-b76e-4149-b4be-a189ca7da142
-- title:
--   Theorem 3.4(iii), p. 9 — under Assumption I and γ < 1/L, φ is level bounded iff φ^DR_γ is
-- statement:
--   Suppose Assumption I holds ($\varphi_1$ $L$-smooth and $\sigma$-hypoconvex with $\sigma\in[-L,L]$, $\varphi_2$ proper lsc, $\operatorname{arg\,min}\varphi\ne\emptyset$). For every $0<\gamma<1/L$,
--   $$\varphi\ \text{is level bounded}\iff\varphi^{\mathrm{DR}}_\gamma\ \text{is level bounded},$$
--   where a function is level bounded if all its sublevel sets $\{x\mid h(x)\le\alpha\}$, $\alpha\in\mathbb R$, are bounded.
--
--   This transfers coercivity of the problem to the envelope, and hence boundedness of the DRS iterates in Theorem 4.3(iii).
--
--   **Formalization Note** Level sets are taken for real $\alpha$, of the `EReal`-valued functions $\varphi$ and $\varphi^{\mathrm{DR}}_\gamma$. $L>0$ is the mission's standing addition; $\gamma<1/L$ is $\gamma L<1$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 9, Theorem 3.4(iii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Theorem 3.4 (iii), p. 9: `φ` is level bounded iff so is `φ^DR_γ`. -/
theorem theorem_3_4_iii {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * L < 1) :
    LevelBounded (phi φ₁ φ₂) ↔ LevelBounded (dre φ₁ φ₂ γ) := by sorry

end NonconvexDRS.DRS
