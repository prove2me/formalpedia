-- Prove2me | Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_3
-- name    : IntroMatrixConc.Submatrix.eq_5_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:27.654651+00:00
-- url     : https://prove2.me/theorems/d07c5496-3404-40dd-a1e6-c814256529df
-- title:
--   (5.2.3), p. 65 — first bound after column selection
-- statement:
--   Let $B\in\mathbb C^{d\times n}$, with $d,n\ge1$. Independently select each row with probability $p/d$ and each column with probability $r/n$, where $0\le p\le d$ and $0\le r\le n$. Write $P$ and $R$ for the resulting diagonal projectors and $Z=PBR$. Then
--
--   $$
--   \mathbb E\|Z\|^2\le1.72\frac rn\,\mathbb E\lambda_{\max}((PB)(PB)^*)+(\log d)\,\mathbb E\max_k\|(PB)_{:k}\|^2.
--   $$
--
--   This is the first of three estimates combined into the row-and-column bound (5.2.2).
--
--   **Formalization Note** The row and column indicators form one jointly independent family. Measurability and integrability of the displayed functions are explicit. Matrices are complex, following the book's general convention.
-- source:
--   Tropp, arXiv:1501.01571v1, (5.2.3), p. 65

import Definitions.Def_IntroMatrixConc_Submatrix_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

namespace IntroMatrixConc.Submatrix

/-- Tropp (5.2.3), p. 65: the first conditional Chernoff bound after column selection. -/
theorem eq_5_2_3 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ)
    (ξ : Fin n → Ω → ℝ) (p r : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hr0 : 0 ≤ r) (hrn : r ≤ (n : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hξMeas : ∀ k, Measurable (ξ k))
    (hIndep : iIndepFun (Sum.elim δ ξ) μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ)))
    (hξ : ∀ k, IsBernoulli μ (ξ k) (r / (n : ℝ))) :
    Integrable (fun ω => spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2) μ ∧
    Integrable (fun ω => lambdaMax (selectedRows B δ ω *
      (selectedRows B δ ω).conjTranspose)) μ ∧
    Integrable (fun ω => maxSelectedColumnSq B δ ω) μ ∧
    (∫ ω, spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2 ∂μ) ≤
      (1.72 : ℝ) * (r / (n : ℝ)) *
        (∫ ω, lambdaMax (selectedRows B δ ω *
          (selectedRows B δ ω).conjTranspose) ∂μ) +
      Real.log d * (∫ ω, maxSelectedColumnSq B δ ω ∂μ) := by sorry

end IntroMatrixConc.Submatrix
