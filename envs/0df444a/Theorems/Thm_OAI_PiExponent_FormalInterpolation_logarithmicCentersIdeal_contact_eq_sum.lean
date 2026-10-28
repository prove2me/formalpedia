-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_contact_eq_sum
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_contact_eq_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:49:00.423107+00:00
-- url     : https://prove2.me/theorems/e717f37a-d86a-48cd-9d9c-ccc9a17c10e8
-- title:
--   Contact of a finite product of logarithmic center ideals is the sum of their contacts
-- statement:
--   For any finite family of logarithmic centers, contact of the product ideal equals the sum of the contacts of the individual center ideals. This applies to the empty family as well as to affine and non-affine curve branches.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleBlowupGeometry.lean (centerIdeal_restrict and affinePolynomialIdeal); Jets/AdmissibleJetSurjectivity.lean (eventual_jetRestriction_surjective); Jets/AffineJetPolynomial.lean (polynomialQuotient_surjective_of_jetRestriction); Approximation/WeightedGlobalSectionBound.lean (eventual_admissible_supportBound).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_contact_eq_sum
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (b : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    polynomialCurveIdealContact b x (logarithmicCentersIdeal c T e) =
      ∑ j, polynomialCurveIdealContact b x (logarithmicCenterIdeal (c j) T e) := by sorry
