-- Prove2me | Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_1_8
-- name    : IntroMatrixConc.Submatrix.eq_5_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:55.546236+00:00
-- url     : https://prove2.me/theorems/0e5eb1f1-5e97-481c-832e-09f7cb8d1522
-- title:
--   (5.1.8), p. 61 — streamlined upper matrix Chernoff expectation bound
-- statement:
--   Let $X_k$ be a finite independent family of measurable, Hermitian, positive semidefinite random $d\times d$ matrices with $d\ge1$ and $\lambda_{\max}(X_k)\le L$ almost surely, where $L\ge0$. Set $Y=\sum_kX_k$ and $\mu_{\max}=\lambda_{\max}(\mathbb EY)$. Then
--
--   $$
--   \mathbb E\lambda_{\max}(Y)\le1.72\,\mu_{\max}+L\log d.
--   $$
--
--   This is the numerical form of the upper expectation estimate in Theorem 5.1.1 and the concentration step used throughout §5.2.
--
--   **Formalization Note** Bounded summands make the displayed eigenvalue integrable; the statement records that fact explicitly. The family may be empty and $L=0$ is allowed.
-- source:
--   Tropp, arXiv:1501.01571v1, (5.1.8), p. 61; Theorem 5.1.1 hypotheses, p. 60

import Definitions.Def_IntroMatrixConc_Submatrix_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

namespace IntroMatrixConc.Submatrix

/-- Tropp (5.1.8), p. 61: the streamlined upper expectation bound. -/
theorem eq_5_1_8 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      (1.72 : ℝ) * lambdaMax (∫ ω, Y ω ∂μ) + L * Real.log d := by sorry

end IntroMatrixConc.Submatrix
