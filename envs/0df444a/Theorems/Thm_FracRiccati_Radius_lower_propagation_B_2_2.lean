-- Prove2me | Theorems.Thm_FracRiccati_Radius_lower_propagation_B_2_2
-- name    : FracRiccati.Radius.lower_propagation_B_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:38.004599+00:00
-- url     : https://prove2.me/theorems/4e9a118f-fc1c-4e4f-adfc-8daafbdaeffe
-- title:
--   §B.2.2, p. 34 — lower-bound propagation b_k ≥ C∗ ρ∗^k k^(α−1) for μ = 0, α ∈ (1, 2]
-- statement:
--   Let $\alpha\in(1,2]$ and let $\lambda,\nu>0$ be real. Let $(a^0_k)$ be the coefficients of $(A_{\lambda,0,\nu})$ and $b_k=a^0_{2k-1}$, $k\ge1$. With $\widetilde B(\alpha)=B(\alpha,\alpha)-2^{1-2\alpha}$, put
--   $$\rho_*=\lambda\nu\,\frac{(2\alpha)^{-\alpha}\widetilde B(\alpha)}{\Gamma(\alpha+1)},\qquad C_*=\frac{(2\alpha)^\alpha}{\lambda\widetilde B(\alpha)}.$$
--   Then
--   $$b_k\ge C_*\,\rho_*^{\,k}\,k^{\alpha-1},\qquad k\ge1.$$
--
--   Via Hadamard's formula this bounds $R_{\psi_{\lambda,0,\nu}}\le\rho_*^{-1/(2\alpha)}$, which yields the upper bound of Theorem 3.3 (b) on $(1,2]$.
--
--   **Formalization Note** The page calls $\rho_*$ "the lowest solution" of the propagation system; it is the admissible value obtained by saturating both constraints, and the statement is the propagated bound itself. The coefficients are real for real parameters; the bound is stated on the real part of the complex coefficient.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 34, §B.2.2 (lower-bound propagation, ρ∗ and C∗)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Definitions.Def_FracRiccati_Radius_Constants

namespace FracRiccati.Radius

theorem lower_propagation_B_2_2 (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (l n : ℝ) (hl : 0 < l) (hn : 0 < n) :
    let ρ : ℝ := l * n * (2 * α) ^ (-α) * BTilde α / Real.Gamma (α + 1)
    let C : ℝ := (2 * α) ^ α / (l * BTilde α)
    ∀ k : ℕ, 1 ≤ k → C * ρ ^ k * (k : ℝ) ^ (α - 1) ≤ (coeff α l 0 n (2 * k - 1)).re := by sorry

end FracRiccati.Radius
