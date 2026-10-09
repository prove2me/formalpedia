-- Prove2me | Theorems.Thm_GaussianMatrix_specNorm_inv_gram_eq
-- name    : GaussianMatrix.specNorm_inv_gram_eq
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:40:42.172299+00:00
-- url     : https://prove2.me/theorems/176e4f39-a944-4528-a89c-b4c4a457c09b
-- title:
--   $\|(AA^\top)^{-1}\|=1/\sigma_{\min}(A^\top)^2$ (with Mathlib's conventions $0^{-1}=0$)
-- statement:
--   Let $A$ be a real $r\times k$ matrix, let $\sigma_{\min}(A^\top)=\inf_{x\in\mathbb R^r,\ \|x\|_2=1}\|A^\top x\|_2$ be the smallest singular value of $A^\top$, and let $\|\cdot\|$ be the spectral ($\ell_2\to\ell_2$ operator) norm. Then
--   $$\big\|(AA^\top)^{-1}\big\|=\frac{1}{\sigma_{\min}(A^\top)^2},$$
--   with the conventions that the inverse of a singular matrix is $0$ and $1/0=0$.
--
--   When $AA^\top$ is invertible this is the statement $\|M^{-1}\|=1/\lambda_{\min}(M)$ for the positive definite matrix $M=AA^\top$, using $\lambda_{\min}(AA^\top)=\min_{\|x\|=1}\|A^\top x\|^2$. When $AA^\top$ is singular, some unit vector $x$ satisfies $A^\top x=0$, so both sides are $0$. It lets you restate any bound on $\lambda_{\min}(GG^\top)$ as a bound on $\|(GG^\top)^{-1}\|$.
--
--   **Formalization Note.** `specNorm` is Mathlib's $\ell_2$ operator norm on matrices and `⁻¹` is Mathlib's total matrix inverse, which is $0$ on singular input. `sMin` is the infimum over the unit sphere, which is $0$ when $r=0$ (empty sphere). Because Lean has $1/0=0$, the identity holds for every $A$ with no hypothesis, including $r=0$.
-- source:
--   standard fact: for a symmetric positive definite matrix M, ‖M⁻¹‖₂ = 1/λ_min(M), and λ_min(AAᵀ) = min_{‖x‖=1} ‖Aᵀx‖² = σ_min(Aᵀ)² (Courant–Fischer; e.g. R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Thm. 4.2.6 and §5.6).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem specNorm_inv_gram_eq {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) :
    specNorm (A * Aᵀ)⁻¹ = 1 / sMin Aᵀ ^ 2 := by sorry

end GaussianMatrix
