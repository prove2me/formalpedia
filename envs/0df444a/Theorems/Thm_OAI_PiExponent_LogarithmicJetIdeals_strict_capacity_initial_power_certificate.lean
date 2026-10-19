-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_initial_power_certificate
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_initial_power_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:47:38.361551+00:00
-- url     : https://prove2.me/theorems/9596dc04-761c-4032-849a-716ca3cf3583
-- title:
--   Strict-capacity finite leading-power certificate for logarithmic jet ideals
-- statement:
--   Under all the original strict-capacity hypotheses, one positive power of the simultaneous logarithmic jet ideal admits a finite monic pure-leading-power certificate with slope strictly below R. This is the remaining geometric obligation; it asserts finite relations rather than normal forms for every power and polynomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_initial_power_certificate
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
    ∃ (ρ : ℝ) (a : ℕ) (N : Fin (d.m + 1) → ℕ)
      (o : MonomialOrder (Fin (d.m + 1)))
      (f : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ),
      0 < ρ ∧ ρ < R ∧ 0 < a ∧
      (∀ i, 0 < N i) ∧
      (∀ i, f i ∈ (simultaneousJetIdeal d.K
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T e) ^ a) ∧
      (∀ i, o.leadingCoeff (f i) = 1) ∧
      (∀ i, o.degree (f i) = Finsupp.single i (N i)) ∧
      (∀ i, (N i : ℝ) *
        InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) i ≤
        (a : ℝ) * ρ) := by sorry
