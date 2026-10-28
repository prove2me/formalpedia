-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_logarithmic_power_generation_from_blowup
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation_from_blowup
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T14:40:04.841635+00:00
-- url     : https://prove2.me/theorems/81f1071f-aed0-49ce-b77c-54628a06d144
-- title:
--   Subcritical generators from admissible blowup geometry
-- statement:
--   For the fixed admissible data and scale hypotheses, some positive power of the logarithmic centers ideal has finite polynomial generators whose weighted degrees are bounded strictly below the corresponding multiple of R.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleBlowupGeometry.lean (centerIdeal_restrict and affinePolynomialIdeal); Jets/AdmissibleJetSurjectivity.lean (eventual_jetRestriction_surjective); Jets/AffineJetPolynomial.lean (polynomialQuotient_surjective_of_jetRestriction); Approximation/WeightedGlobalSectionBound.lean (eventual_admissible_supportBound).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation_from_blowup
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Real, D < (s : Real) * (R : Real) ∧
      ∃ S : Finset (MvPolynomial (Fin (d.m + 1)) Complex),
        Ideal.span (S : Set (MvPolynomial (Fin (d.m + 1)) Complex)) =
          (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ P ∈ S, ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D := by sorry
