-- Prove2me | Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_4
-- name    : IntroMatrixConc.Submatrix.eq_5_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:06.096974+00:00
-- url     : https://prove2.me/theorems/daba5df4-6e22-4d1a-8314-a2f45181e418
-- title:
--   (5.2.4), p. 66 — expected spectral norm after row selection
-- statement:
--   Let $B\in\mathbb C^{d\times n}$, with $d,n\ge1$, and let $P$ independently select rows with Bernoulli probability $p/d$, where $0\le p\le d$. Then
--
--   $$
--   \mathbb E\lambda_{\max}((PB)(PB)^*)\le1.72\frac pd\lambda_{\max}(B^*B)+(\log n)\max_j\|b_{j:}\|^2.
--   $$
--
--   This estimates the first expectation on the right side of (5.2.3).
--
--   **Formalization Note** The matrix is complex and the row indicators are measurable. Their bounded support supplies integrability, which is also an explicit conclusion. The maxima range over nonempty finite index sets.
-- source:
--   Tropp, arXiv:1501.01571v1, (5.2.4), p. 66

import Definitions.Def_IntroMatrixConc_Submatrix_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

namespace IntroMatrixConc.Submatrix

/-- Tropp (5.2.4), p. 66: the second Chernoff bound after row selection. -/
theorem eq_5_2_4 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hIndep : iIndepFun δ μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ))) :
    Integrable (fun ω => lambdaMax (selectedRows B δ ω *
      (selectedRows B δ ω).conjTranspose)) μ ∧
    (∫ ω, lambdaMax (selectedRows B δ ω *
      (selectedRows B δ ω).conjTranspose) ∂μ) ≤
      (1.72 : ℝ) * (p / (d : ℝ)) * lambdaMax (B.conjTranspose * B) +
        Real.log n * maxRowSq B := by sorry

end IntroMatrixConc.Submatrix
