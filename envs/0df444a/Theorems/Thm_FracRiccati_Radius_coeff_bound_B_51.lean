-- Prove2me | Theorems.Thm_FracRiccati_Radius_coeff_bound_B_51
-- name    : FracRiccati.Radius.coeff_bound_B_51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:01.490969+00:00
-- url     : https://prove2.me/theorems/cdea22c1-36dc-489f-9e31-cfa9ea922702
-- title:
--   (B.51), p. 33 — coefficient upper bound |a_k| ≤ C∗ k^(α−1) ρ∗^k for α ∈ (1, 2]
-- statement:
--   Let $\alpha\in(1,2]$ and $\lambda,\mu,\nu\in\mathbb C$ with $\lambda\nu\ne0$, and let $(a_k)$ be the coefficients of $(A_{\lambda,\mu,\nu})$ (3.19). Put
--   $$\rho_*=\frac{|\mu|+\sqrt{|\mu|^2+\frac{2^{2(2-\alpha)}\alpha^{\alpha-1}|\lambda||\nu|}{\Gamma(\alpha)}}}{2\alpha^\alpha},\qquad C_*=\frac{|\nu|}{\Gamma(\alpha+1)\rho_*}. \qquad (B.51)$$
--   Then the upper bound (B.42) propagates:
--   $$\forall k\ge1,\qquad |a_k|\le C_*\,k^{\alpha-1}\rho_*^{\,k}.$$
--
--   As the paper notes, this gives $R_\psi\ge\rho_*^{-1/\alpha}=\tau_*$ on $(1,2]$, i.e. Theorem 3.3 (a) for $\alpha>1$.
--
--   **Formalization Note** $\mu^2$ is read as $|\mu|^2$, as in (B.48). The hypotheses $\lambda\ne0$, $\nu\ne0$ are Assumption 3.1 and make $\rho_*>0$. The radius consequence printed after (B.51) is the goal theorem and is not repeated here.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 33, §B.2.1, (B.42), (B.51)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem coeff_bound_B_51 (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α)) / (2 * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k := by sorry

end FracRiccati.Radius
