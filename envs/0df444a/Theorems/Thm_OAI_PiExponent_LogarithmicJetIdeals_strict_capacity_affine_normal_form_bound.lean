-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_affine_normal_form_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_affine_normal_form_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T23:02:23.48674+00:00
-- url     : https://prove2.me/theorems/a6a1a765-0a2a-4517-942b-9cd655fec7b7
-- title:
--   Uniform affine weighted normal-form bound for simultaneous logarithmic ideal powers
-- statement:
--   Under the exact strict-capacity hypotheses, all quotient classes modulo simultaneous logarithmic ideal powers admit representatives with one uniform affine weighted-degree bound, whose slope is strictly smaller than R. This is the main geometric regularity obligation. The offset accommodates small powers; at k=0 the ideal power is the whole ring and Q=0 suffices. All positivity, common-scale, capacity, and strict truncation assumptions are retained.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_affine_normal_form_bound
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ < R ∧ 0 ≤ B ∧
      ∀ k : ℕ, ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
          (∀ u ∈ Q.support,
            (∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
              (u i : ℝ)) ≤ (k : ℝ) * ρ + B) ∧
          P - Q ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d)) T e) ^ k := by sorry
