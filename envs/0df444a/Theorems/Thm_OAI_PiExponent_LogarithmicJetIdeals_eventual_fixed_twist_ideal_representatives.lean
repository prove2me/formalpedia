-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_fixed_twist_ideal_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.eventual_fixed_twist_ideal_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T17:33:41.303932+00:00
-- url     : https://prove2.me/theorems/022db905-3a5f-400a-8c70-602cf279e920
-- title:
--   Eventual bounded representatives with a fixed additional jet-ideal power
-- statement:
--   For each admissible datum, choose one positive scale and fixed logarithmic jet ideal whose generators vanish to at least that scale. For every fixed additional ideal power B, every polynomial has, for all sufficiently large k, a representative of column weight at most kS modulo the (k+B)-th power of that ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.eventual_fixed_twist_ideal_representatives
    {nu : ℝ} (d : FixedData nu) :
    ∃ S : ℝ, 0 < S ∧
      ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ,
        (∀ i, 0 < e i) ∧
        (∀ i, S ≤ (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        (∀ i : Fin d.m,
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
              (T i : ℝ) * (d.v0 : ℝ)) ∧
        ∀ B : ℕ, ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
          ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
            ∃ Q : WeightedPolynomial d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) ((k : ℝ) * S),
              P - Q.val ∈ (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
                T e) ^ (k + B) := by sorry
