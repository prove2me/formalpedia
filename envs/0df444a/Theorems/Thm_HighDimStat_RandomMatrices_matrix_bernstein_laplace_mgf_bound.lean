-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_matrix_bernstein_laplace_mgf_bound
-- name    : HighDimStat.RandomMatrices.matrix_bernstein_laplace_mgf_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:05:38.063838+00:00
-- url     : https://prove2.me/theorems/338b6cf5-eb31-4126-b38d-29502bbf3fa9
-- title:
--   Matrix Bernstein Laplace transform MGF tail bound
-- statement:
--   For independent zero-mean symmetric random matrices $Q_1, \dots, Q_n$ satisfying the matrix Bernstein moment condition with parameter $b > 0$, applying the matrix Laplace transform method and Lieb's theorem for every $t \in (0, 1/b)$ bounds the spectral-norm tail probability by $2 \operatorname{rank}(\sum_{i=1}^n \operatorname{var}(Q_i)) \exp(-n t \delta + \frac{t^2}{2(1 - tb)} \|\sum_{i=1}^n \operatorname{var}(Q_i)\|_2)$.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Proof of Theorem 6.17, pp. 176-177

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

noncomputable instance instMeasurableSpaceMatrixLaplace {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  unfold Matrix; infer_instance

theorem matrix_bernstein_laplace_mgf_bound {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht₀ : 0 < t) (htb : t * b < 1) :
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * t * δ) +
          t ^ 2 / (2 * (1 - t * b)) * opNorm (∑ i, matrixVariance (Q i) Prob)) := by sorry

end HighDimStat.RandomMatrices
