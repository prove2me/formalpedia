-- Prove2me | Theorems.Thm_FracRiccati_Radius_prop_B_1_a
-- name    : FracRiccati.Radius.prop_B_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:00.129088+00:00
-- url     : https://prove2.me/theorems/4c045d4b-63c1-41b5-8502-97143a85b663
-- title:
--   Proposition B.1(a) = Theorem 3.3(d), pp. 9, 29 — for μ = 0 the even coefficients vanish and b_k = a⁰_{2k−1} solves (B.50)
-- statement:
--   Let $\alpha>0$ and $\lambda,\nu\in\mathbb C$ with $\lambda\nu\ne0$, and let $(a^0_k)_{k\ge0}$ be the solution of $(A_{\lambda,0,\nu})$, i.e. the coefficients (3.19) with $\mu=0$. Then:
--
--   1. $a^0_{2k}=0$ for every $k\ge1$;
--   2. $(a^0)^{*2}_{2k-1}=\sum_{\ell=1}^{2k-2}a^0_\ell a^0_{2k-1-\ell}=0$ for every $k\ge1$;
--   3. the sequence $b_k=a^0_{2k-1}$, $k\ge1$, solves
--   $$b_1=\frac{\nu}{\Gamma(\alpha+1)}\qquad\text{and}\qquad b_{k+1}=\lambda\,\frac{\Gamma(2\alpha k+1)}{\Gamma((2k+1)\alpha+1)}\,b^{*2}_{k+1},\quad k\ge1, \qquad (B.50)$$
--   where $b^{*2}_{k+1}=\sum_{\ell=1}^{k}b_\ell\,b_{k+1-\ell}$ is the convolution (3.20).
--
--   The odd subsequence is the object of the lower-bound propagation of §B.1.2 and §B.2.2, which bounds the radius $R_{\psi_{\lambda,0,\nu}}$ from above.
--
--   **Formalization Note** The paper states Proposition B.1 for real $\lambda,\mu,\nu$ and Theorem 3.3 (d) for complex ones; the claim is algebraic and is stated for complex $\lambda,\nu$. The hypotheses $\lambda\ne0$, $\nu\ne0$ are the paper's standing Assumption 3.1. $b_\ell$ is written as `coeff α lam 0 nu (2ℓ-1)`; every natural subtraction in the statement is applied to indices $\ge1$.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 29, Proposition B.1 (a), (B.50); p. 9, Theorem 3.3 (d), (3.23)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem prop_B_1_a (α : ℝ) (hα0 : 0 < α) (lam nu : ℂ) (hlam : lam ≠ 0) (hnu : nu ≠ 0) :
    (∀ k : ℕ, 1 ≤ k → coeff α lam 0 nu (2 * k) = 0) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ ℓ ∈ Finset.Ico 1 (2 * k - 1), coeff α lam 0 nu ℓ * coeff α lam 0 nu (2 * k - 1 - ℓ) = 0) ∧
    coeff α lam 0 nu (2 * 1 - 1) = nu / (Real.Gamma (α + 1) : ℂ) ∧
    (∀ k : ℕ, 1 ≤ k →
      coeff α lam 0 nu (2 * (k + 1) - 1) =
        lam * ((Real.Gamma (2 * α * k + 1) / Real.Gamma ((2 * k + 1) * α + 1) : ℝ) : ℂ) *
          ∑ ℓ ∈ Finset.Ico 1 (k + 1),
            coeff α lam 0 nu (2 * ℓ - 1) * coeff α lam 0 nu (2 * (k + 1 - ℓ) - 1)) := by sorry

end FracRiccati.Radius
