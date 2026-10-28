-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_contact_cutoff_invariance
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_contact_cutoff_invariance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:40:23.352963+00:00
-- url     : https://prove2.me/theorems/918157a7-e5b8-485a-929f-9d0857b181ec
-- title:
--   Curve contact is invariant under admissible logarithm cutoffs
-- statement:
--   For positive commensurable jet weights, every cutoff satisfying the non-strict weighted threshold gives the same placewise contact as the canonical cutoff e₀.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleBlowupGeometry.lean (centerIdeal_restrict and affinePolynomialIdeal); Jets/AdmissibleJetSurjectivity.lean (eventual_jetRestriction_surjective); Jets/AffineJetPolynomial.lean (polynomialQuotient_surjective_of_jetRestriction); Approximation/WeightedGlobalSectionBound.lean (eventual_admissible_supportBound).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_contact_cutoff_invariance
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (T : Fin m → Nat)
    (hT : ∀ i, (v i.succ : Real) ≤ (T i : Real) * (v 0 : Real))
    (E : Type) [Field E] [Algebra Complex E]
    (b : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    polynomialCurveIdealContact b x (logarithmicCentersIdeal c T e) =
      polynomialCurveIdealContact b x
        (logarithmicCentersIdeal c (fun _ => e 0) e) := by sorry
