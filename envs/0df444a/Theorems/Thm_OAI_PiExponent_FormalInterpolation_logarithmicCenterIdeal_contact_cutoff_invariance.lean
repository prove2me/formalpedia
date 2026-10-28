-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_contact_cutoff_invariance
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_contact_cutoff_invariance
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:45:30.281316+00:00
-- url     : https://prove2.me/theorems/95fbd790-b0bc-48b9-9843-7429e48284cd
-- title:
--   Single-center contact is invariant under an admissible logarithm cutoff
-- statement:
--   For one logarithmic center, the weighted cutoff condition ensures that replacing the coordinate truncations by the common canonical cutoff `e 0` does not change contact along any normalized curve place. The strict-order comparison handles the non-strict boundary case by capping the minimum at the base-coordinate generator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleBlowupGeometry.lean (centerIdeal_restrict and affinePolynomialIdeal); Jets/AdmissibleJetSurjectivity.lean (eventual_jetRestriction_surjective); Jets/AffineJetPolynomial.lean (polynomialQuotient_surjective_of_jetRestriction); Approximation/WeightedGlobalSectionBound.lean (eventual_admissible_supportBound).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_contact_cutoff_invariance
    {m : Nat} (c : Fin m → Complex)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (T : Fin m → Nat)
    (hT : ∀ i, (v i.succ : Real) ≤ (T i : Real) * (v 0 : Real))
    (E : Type) [Field E] [Algebra Complex E]
    (b : OAI.PiExponent.FormalInterpolation.PolynomialCurvePlace E)
    (x : Fin (m + 1) → E) :
    OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact b x
        (OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal c T e) =
      OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact b x
        (OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal c (fun _ => e 0) e) := by sorry
