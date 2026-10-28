-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_fibre_nonconstant_contact_bound
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_nonconstant_contact_bound
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:17:06.214339+00:00
-- url     : https://prove2.me/theorems/cd83957f-b27c-4608-99e9-1aee1215de4a
-- title:
--   Fibre contact bound when all positive coordinates are transcendental
-- statement:
--   On the fibre x_0=1, under fibre-volume and separation hypotheses, if every positive-index coordinate is transcendental over C, then the total contact of the logarithmic centers ideal is at most R/(1+sigma) times the weighted pole degree. Failure of this bound forces some coordinate to be constant.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_nonconstant_contact_bound
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hfibreVolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ m *
        (∏ i : Fin m, (w i.succ : Real)) /
          (∏ i : Fin m, (v i.succ : Real)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ)) :
    (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) ≤
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by sorry
