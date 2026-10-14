-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_bounded_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.eventual_bounded_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-12T20:16:12.750073+00:00
-- url     : https://prove2.me/theorems/625b0afe-4068-4802-a072-c937125f3981
-- title:
--   Eventual bounded representatives modulo logarithmic jet ideal powers
-- statement:
--   For every fixed admissible datum, choose a positive rational radius and polynomial jet ideals whose generators have row-weight order at least that radius. For all sufficiently large n, every polynomial class modulo the nth power of the simultaneous jet ideal has a representative satisfying the column-weight degree bound nR.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.eventual_bounded_representatives
    {nu : ℝ} (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ, ∃ N : ℕ,
      (∀ i, (R : ℝ) ≤ (e i : ℝ) *
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
      (∀ i : Fin d.m,
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
            (T i : ℝ) * (d.v0 : ℝ)) ∧
      ∀ n : ℕ, N ≤ n → ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ n := by sorry
