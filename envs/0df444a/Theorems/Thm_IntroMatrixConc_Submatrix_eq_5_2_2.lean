-- Prove2me | Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_2_2
-- name    : IntroMatrixConc.Submatrix.eq_5_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:10.978632+00:00
-- url     : https://prove2.me/theorems/ee5ba0cf-3a7d-4c33-9c15-10dd66e3f7cb
-- title:
--   (5.2.2), p. 65 — expected squared norm of a random row-and-column submatrix
-- statement:
--   Let $B\in\mathbb C^{d\times n}$, with $d,n\ge1$. Independently select its rows with probability $p/d$ and its columns with probability $r/n$, where $0\le p\le d$ and $0\le r\le n$. Let $P$ and $R$ be the diagonal zero-one projectors recording the selections, and set $Z=PBR$. Then
--
--   $$
--   \begin{aligned}
--   \mathbb E\|Z\|^2\le{}&3\frac pd\frac rn\|B\|^2
--   +2\frac{p\log d}{d}\max_k\|b_{:k}\|^2\\
--   &+2\frac{r\log n}{n}\max_j\|b_{j:}\|^2
--   +(\log d)(\log n)\max_{j,k}|b_{jk}|^2.
--   \end{aligned}
--   $$
--
--   The estimate separates a term involving the whole matrix from fluctuations controlled by its largest column, row, and entry.
--
--   **Formalization Note** The indicators for all rows and columns are one jointly independent measurable family. The book's simplified constants $3$ and $2$ are used exactly. Integrability of $\|Z\|^2$ is asserted explicitly under the bounded Bernoulli model; $d,n\ge1$ keep every maximum and logarithm in its intended domain.
-- source:
--   Tropp, arXiv:1501.01571v1, (5.2.2), p. 65; simplification note, p. 66

import Definitions.Def_IntroMatrixConc_Submatrix_Defs

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

namespace IntroMatrixConc.Submatrix

/-- Tropp (5.2.2), p. 65: the row-and-column random submatrix expectation bound. -/
theorem eq_5_2_2 {Ω : Type*} [MeasurableSpace Ω]
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
    (∫ ω, spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2 ∂μ) ≤
      (3 : ℝ) * (p / (d : ℝ)) * (r / (n : ℝ)) * spectralNorm B ^ 2 +
      2 * (p * Real.log d / (d : ℝ)) * maxColumnSq B +
      2 * (r * Real.log n / (n : ℝ)) * maxRowSq B +
      Real.log d * Real.log n * maxEntrySq B := by sorry

end IntroMatrixConc.Submatrix
