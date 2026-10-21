-- Prove2me | Theorems.Thm_FracRiccati_Radius_lower_propagation_B_1_2
-- name    : FracRiccati.Radius.lower_propagation_B_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:28.197976+00:00
-- url     : https://prove2.me/theorems/62c7da5f-a036-44a5-8d6d-357fad985b6d
-- title:
--   §B.1.2, pp. 31–32 — lower-bound propagation b_k ≥ c∗ ρ∗^k k^(α−1) for μ = 0, α ∈ (0, 1]
-- statement:
--   Let $\alpha\in(0,1]$ and let $\lambda,\nu>0$ be real. Let $(a^0_k)$ be the coefficients of $(A_{\lambda,0,\nu})$ and $b_k=a^0_{2k-1}$, $k\ge1$, its non-zero subsequence. Put
--   $$\rho^*=\frac{5^{1-\alpha}}{3}\,\frac{\alpha^{-\alpha}\,\lambda\nu}{\Gamma(\alpha+1)},\qquad c^*=\frac{\nu}{\rho^*\alpha\Gamma(\alpha)}.$$
--   Then
--   $$b_k\ge c^*\,(\rho^*)^k\,k^{\alpha-1},\qquad k\ge1.$$
--
--   Via Hadamard's formula, this gives $R_{\psi_{\lambda,0,\nu}}\le(\rho^*)^{-1/(2\alpha)}=\big(\tfrac{3}{5^{1-\alpha}}\big)^{\frac1{2\alpha}}\sqrt\alpha\,\big(\tfrac{\Gamma(\alpha+1)}{\lambda\nu}\big)^{\frac1{2\alpha}}$, the upper bound of Theorem 3.3 (b) on $(0,1]$.
--
--   **Formalization Note** Page 32 typesets $\lambda\nu$ in the denominator of $\rho^*$. The preceding line ($\rho\le2^{2-3\alpha}\frac{\alpha^{-(1+\alpha)}}{\Gamma(\alpha)}\lambda\nu\,\tilde b_k$ with $\min_k\tilde b_k=2^{3\alpha-2}5^{1-\alpha}/3$) and the final bound $R\le(3/5^{1-\alpha})^{1/(2\alpha)}\alpha^{1/2+1/(2\alpha)}\Gamma(\alpha)^{1/(2\alpha)}/(\lambda\nu)^{1/(2\alpha)}$ both require $\lambda\nu$ in the numerator, which is how $\rho^*$ is stated here. The coefficients are real for real parameters; the bound is stated on the real part of the complex coefficient.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, pp. 31–32, §B.1.2 (lower-bound propagation, ρ∗ and c∗)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem lower_propagation_B_1_2 (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (l n : ℝ) (hl : 0 < l) (hn : 0 < n) :
    let ρ : ℝ := (5 : ℝ) ^ (1 - α) / 3 * α ^ (-α) * (l * n) / Real.Gamma (α + 1)
    let c : ℝ := n / (ρ * α * Real.Gamma α)
    ∀ k : ℕ, 1 ≤ k → c * ρ ^ k * (k : ℝ) ^ (α - 1) ≤ (coeff α l 0 n (2 * k - 1)).re := by sorry

end FracRiccati.Radius
