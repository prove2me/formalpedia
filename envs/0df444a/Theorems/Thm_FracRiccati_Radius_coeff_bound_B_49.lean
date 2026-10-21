-- Prove2me | Theorems.Thm_FracRiccati_Radius_coeff_bound_B_49
-- name    : FracRiccati.Radius.coeff_bound_B_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:04.031776+00:00
-- url     : https://prove2.me/theorems/85eddb23-ae41-4f60-aa07-57440e86dfa0
-- title:
--   (B.48)–(B.49), p. 28 — coefficient upper bound |a_k| ≤ C∗ k^(α−1) ρ∗^k for α ∈ (0, 1]
-- statement:
--   Let $\alpha\in(0,1]$ and $\lambda,\mu,\nu\in\mathbb C$ with $\lambda\nu\ne0$, and let $(a_k)$ be the coefficients of $(A_{\lambda,\mu,\nu})$ (3.19). Put
--   $$\rho_*=\frac{|\mu|+\sqrt{|\mu|^2+2^{\,2-(1-2\alpha)_+}\frac{\alpha^{\alpha-1}\Gamma(\alpha)}{\Gamma(2\alpha)}|\lambda||\nu|}}{2^{\,1-(1-2\alpha)_+}\alpha^\alpha} \quad (B.48),\qquad C_*=\frac{|\nu|}{\Gamma(\alpha+1)\rho_*}.$$
--   Then
--   $$\forall k\ge1,\qquad |a_k|\le C_*\,k^{\alpha-1}\rho_*^{\,k}. \qquad (B.49)$$
--
--   Since $\rho_*^{-1/\alpha}=\tau_*$ for $\alpha\le1$, Hadamard's formula turns (B.49) into the lower bound $R_{\psi_{\lambda,\mu,\nu}}\ge\tau_*$ of Theorem 3.3 (a) on $(0,1]$.
--
--   **Formalization Note** The page writes $\mu^2$ under the root; it is $|\mu|^2$ here, as $\rho_*$ is the positive root of $2^{-(1-2\alpha)_+}\alpha^\alpha\rho^2-|\mu|\rho-\frac{|\lambda||\nu|\Gamma(\alpha)}{\alpha\Gamma(2\alpha)}=0$ (p. 28). The hypotheses $\lambda\ne0$, $\nu\ne0$ are Assumption 3.1 (p. 7) and make $\rho_*>0$. $\rho_*^k$ is a natural power, $k^{\alpha-1}$ a real power.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 28, §B.1.1, (B.48), (B.49)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem coeff_bound_B_49 (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (lam mu nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    let ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖)) /
        ((2 : ℝ) ^ (1 - max (1 - 2 * α) 0) * α ^ α)
    let C : ℝ := ‖nu‖ / (Real.Gamma (α + 1) * ρ)
    ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤ C * (k : ℝ) ^ (α - 1) * ρ ^ k := by sorry

end FracRiccati.Radius
