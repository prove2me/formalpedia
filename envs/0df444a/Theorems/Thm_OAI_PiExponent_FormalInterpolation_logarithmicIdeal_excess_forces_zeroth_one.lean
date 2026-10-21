-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_excess_forces_zeroth_one
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicIdeal_excess_forces_zeroth_one
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T22:33:54.785637+00:00
-- url     : https://prove2.me/theorems/bf2493a3-f9e8-46aa-ae6a-918100408902
-- title:
--   Excess logarithmic ideal contact forces the zeroth coordinate to equal one
-- statement:
--   Under positivity, full-dimensional volume, separated-product, center-injectivity, and exact scale hypotheses, excessive contact with the canonical truncated logarithmic center ideal forces the zeroth curve coordinate to be identically one. No fibre-volume or coordinate-ratio hypothesis is assumed. Prove this by the local ideal/contact comparison followed by the source logarithmic auxiliary-polynomial, derivative-vanishing, and persistent-comparison argument. The strict cutoff remains exactly e₀.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicIdeal_excess_forces_zeroth_one
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hvolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
        (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1)
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
    (hexcess :
      (R : Real) * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
        (1 + (sigma : Real)) *
          (∑ᶠ nu : PolynomialCurvePlace E,
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    x 0 = 1 := by sorry
