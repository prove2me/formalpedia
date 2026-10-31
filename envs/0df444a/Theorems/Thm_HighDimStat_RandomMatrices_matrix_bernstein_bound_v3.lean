-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_matrix_bernstein_bound_v3
-- name    : HighDimStat.RandomMatrices.matrix_bernstein_bound_v3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:16:30.684005+00:00
-- url     : https://prove2.me/theorems/f418c291-ab9e-432f-8ae2-e21d90980c12
-- title:
--   Bernstein bound for random matrices (Theorem 6.17)
-- statement:
--   For independent zero-mean symmetric random matrices $Q_1, \dots, Q_n$ satisfying the matrix Bernstein condition with parameter $b > 0$, for every $\delta > 0$, the spectral-norm tail probability satisfies $\mathbb{P}[\frac{1}{n}\|\sum_{i=1}^n Q_i\|_2 \ge \delta] \le 2 \operatorname{rank}(\sum_{i=1}^n \operatorname{var}(Q_i)) \exp(-\frac{n\delta^2}{2(\sigma^2 + b\delta)})$, where $\sigma^2 := \frac{1}{n}\|\sum_{i=1}^n \operatorname{var}(Q_i)\|_2$.
--
--   **Formalization Note** Moves `instMeasurableSpaceMatrix` from `formal_statement` into `preamble` using `inferInstanceAs` so that `formal_statement` contains a single `:= by sorry` block compatible with the platform verifier.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Theorem 6.17, p. 176, Eq. (6.42)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_LoewnerLE
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

noncomputable instance instMeasurableSpaceMatrixV3 {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

end HighDimStat.RandomMatrices

namespace HighDimStat.RandomMatrices

theorem matrix_bernstein_bound_v3 {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * δ ^ 2) /
          (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ))) := by sorry

end HighDimStat.RandomMatrices
