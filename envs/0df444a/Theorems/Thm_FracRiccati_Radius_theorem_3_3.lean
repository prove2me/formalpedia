-- Prove2me | Theorems.Thm_FracRiccati_Radius_theorem_3_3
-- name    : FracRiccati.Radius.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:27.290992+00:00
-- url     : https://prove2.me/theorems/b706d1b6-e171-4ae2-9538-b9d047434738
-- title:
--   Theorem 3.3 (a)–(b), p. 9 — explicit lower bound τ∗ ≤ R_ψ and upper bound R_ψ ≤ C_α (Γ(α+1)/(λν))^(1/(2α)) on the convergence radius
-- statement:
--   Let $\alpha\in(0,2]$. For parameters $\lambda,\mu,\nu$ let $(a_k)$ be the coefficients (3.19) of the fractional power series $\psi_{\lambda,\mu,\nu}(t)=\sum_k a_kt^{k\alpha}$ solving the fractional Riccati equation with zero initial condition, and $R_{\psi_{\lambda,\mu,\nu}}=\liminf_k|a_k|^{-1/(\alpha k)}$ its convergence radius (3.21).
--
--   1. **General lower bound.** For all $\lambda,\mu,\nu\in\mathbb C$ with $\lambda\ne0$ and $\nu\ne0$,
--   $$R_{\psi_{\lambda,\mu,\nu}}\ge\tau_*:=\frac{2^{\frac1\alpha-(\frac1\alpha-2)_+}\,\alpha}{\Big(|\mu|+\sqrt{|\mu|^2+c_\alpha\frac{|\lambda||\nu|}{\Gamma(\alpha)}}\Big)^{1/\alpha}}>0,\qquad c_\alpha=2^{2-(1-2\alpha)_+-2(\alpha-1)_+}\alpha^{\alpha-1}B(\alpha\wedge1,\alpha\wedge1).$$
--   2. **Upper bound.** If $\lambda,\nu>0$ and $\mu\ge0$ (resp. $\lambda,\nu<0$ and $\mu\le0$) are real, then
--   $$R_{\psi_{\lambda,\mu,\nu}}\le R_{\psi_{|\lambda|,0,|\nu|}}\le C_\alpha\Big(\frac{\Gamma(\alpha+1)}{\lambda\nu}\Big)^{\frac1{2\alpha}},\qquad C_\alpha=\begin{cases}(3\cdot5^{\alpha-1})^{\frac1{2\alpha}}\sqrt\alpha,&\alpha\in(0,1],\\ \sqrt{2\alpha}/\widetilde B(\alpha),&\alpha\in(1,2],\end{cases}$$
--   with $\widetilde B(\alpha)=B(\alpha,\alpha)-2^{1-2\alpha}$.
--
--   The theorem gives an explicit interval, depending only on $\alpha$ and the parameters, inside which the fractional power series converges, and, for parameters of equal sign, the order $(\lambda\nu)^{-1/(2\alpha)}$ of the radius. In the rough Heston model this tells when the power series alone can be used for the characteristic function, and where the hybrid numerical scheme of the paper must take over.
--
--   **Formalization Note** The statement is about the coefficient sequence and its Hadamard radius, computed in $[0,\infty]$; the real bounds enter through `ENNReal.ofReal`. Deviations from the page: (i) the page's "$\alpha\in[0,2]$" is read as $0<\alpha\le2$, since $1/\alpha$ appears; (ii) $\nu\ne0$ is the paper's standing Assumption 3.1 ($\lambda\nu\ne0$, p. 7), and without it $\tau_*$ may be $0/0$; (iii) $\mu^2$ is read as $|\mu|^2$, the proof's quadratic having coefficient $|\mu|$; (iv) the page prints the strict inequality $R>\tau_*$, while the proof (p. 29 and after (B.51)) establishes only $R\ge\tau_*$, so the non-strict inequality is stated; (v) the "Moreover" sentence of (b), on monotonicity and blow-up of the maximal Riccati solution, is not formalized. In (b) the real parameters are cast to $\mathbb C$, and $\lambda\nu=|\lambda||\nu|>0$ in both sign cases.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 9, Theorem 3.3 (a), (b), (3.22); Assumption 3.1, p. 7

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Definitions.Def_FracRiccati_Radius_Constants

namespace FracRiccati.Radius

theorem theorem_3_3 (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2) :
    (∀ lam mu nu : ℂ, lam ≠ 0 → nu ≠ 0 →
        0 < tauStar α lam mu nu ∧
        ENNReal.ofReal (tauStar α lam mu nu) ≤ radius α (coeff α lam mu nu)) ∧
    (∀ l m n : ℝ, ((0 < l ∧ 0 < n ∧ 0 ≤ m) ∨ (l < 0 ∧ n < 0 ∧ m ≤ 0)) →
        radius α (coeff α l m n) ≤ radius α (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ)) ∧
        radius α (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ)) ≤
          ENNReal.ofReal (CAlpha α * (Real.Gamma (α + 1) / (l * n)) ^ (1 / (2 * α)))) := by sorry

end FracRiccati.Radius
