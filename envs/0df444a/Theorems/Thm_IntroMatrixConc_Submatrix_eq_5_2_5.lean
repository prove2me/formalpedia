-- Prove2me | Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_5
-- name    : IntroMatrixConc.Submatrix.eq_5_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:09.599526+00:00
-- url     : https://prove2.me/theorems/3f04c09b-01e7-464c-a5d3-a5a6ee75ee3e
-- title:
--   (5.2.5), p. 66 — expected largest sampled column norm
-- statement:
--   Let $B\in\mathbb C^{d\times n}$, with $d,n\ge1$, and let $P$ independently select rows with Bernoulli probability $p/d$, where $0\le p\le d$. Then
--
--   $$
--   \mathbb E\max_k\|(PB)_{:k}\|^2\le1.72\frac pd\max_k\|b_{:k}\|^2+(\log n)\max_{j,k}|b_{jk}|^2.
--   $$
--
--   This controls the remaining expectation in (5.2.3), involving the largest sampled column.
--
--   **Formalization Note** The maxima are finite and nonempty, and the bounded Bernoulli model makes the sampled-column maximum integrable; that fact is stated explicitly.
-- source:
--   Tropp, arXiv:1501.01571v1, (5.2.5), p. 66

import Definitions.Def_IntroMatrixConc_Submatrix_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

namespace IntroMatrixConc.Submatrix

/-- Tropp (5.2.5), p. 66: the maximum sampled column norm. -/
theorem eq_5_2_5 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hIndep : iIndepFun δ μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ))) :
    Integrable (fun ω => maxSelectedColumnSq B δ ω) μ ∧
    (∫ ω, maxSelectedColumnSq B δ ω ∂μ) ≤
      (1.72 : ℝ) * (p / (d : ℝ)) * maxColumnSq B +
        Real.log n * maxEntrySq B := by sorry

end IntroMatrixConc.Submatrix
