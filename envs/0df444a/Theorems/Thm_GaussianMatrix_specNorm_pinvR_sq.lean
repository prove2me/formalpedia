-- Prove2me | Theorems.Thm_GaussianMatrix_specNorm_pinvR_sq
-- name    : GaussianMatrix.specNorm_pinvR_sq
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:42:20.503419+00:00
-- url     : https://prove2.me/theorems/5f457ce8-0f44-419b-88ff-a3e56b89684c
-- title:
--   $\|A^\dagger\|^2=\|(AA^\top)^{-1}\|$ for $A^\dagger=A^\top(AA^\top)^{-1}$
-- statement:
--   Let $A$ be a real $r\times k$ matrix and let $A^\dagger=A^\top(AA^\top)^{-1}$ be its right pseudoinverse, where the inverse of a singular matrix is taken to be $0$. Then, in the spectral norm,
--   $$\|A^\dagger\|^2=\big\|(AA^\top)^{-1}\big\|.$$
--
--   Write $M=AA^\top$, which is symmetric. By the $C^*$-identity $\|B\|^2=\|B^\top B\|$ we get $(A^\dagger)^\top A^\dagger=M^{-1}AA^\top M^{-1}=M^{-1}MM^{-1}=M^{-1}$. If $M$ is singular, both sides are $0$. Together with $\|(AA^\top)^{-1}\|=1/\sigma_{\min}(A^\top)^2$ this gives $\|A^\dagger\|=1/\sigma_{\min}(A^\top)$, which turns tail bounds for $\lambda_{\min}(GG^\top)$ into tail bounds for $\|G^\dagger\|$.
--
--   **Formalization Note.** `pinvR A = Aᵀ * (A * Aᵀ)⁻¹` uses Mathlib's total inverse, and `specNorm` is the $\ell_2$ operator norm. The identity holds unconditionally.
-- source:
--   standard fact: C*-identity ‖B‖² = ‖BᵀB‖ for the spectral norm, applied to B = Aᵀ(AAᵀ)⁻¹, for which BᵀB = (AAᵀ)⁻¹ (e.g. N. Halko, P.-G. Martinsson, J. A. Tropp, SIAM Review 53 (2011), §A.2, ‖G†‖ = σ_min(G)⁻¹).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem specNorm_pinvR_sq {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ) :
    specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹ := by sorry

end GaussianMatrix
