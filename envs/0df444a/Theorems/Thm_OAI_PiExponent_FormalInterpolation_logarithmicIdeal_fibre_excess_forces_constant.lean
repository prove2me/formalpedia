-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_fibre_excess_forces_constant
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_excess_forces_constant
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T22:34:12.715863+00:00
-- url     : https://prove2.me/theorems/38021cce-df38-4c4a-9de6-c0ac1a941867
-- title:
--   Excess contact on the unit fibre forces a constant coordinate
-- statement:
--   On the fibre x₀=1, fibre volume and separated products force some positive-index coordinate to be constant whenever canonical ideal contact is excessive. Full-dimensional volume and coordinate ratios are not assumed. All logarithmic corrections vanish on this fibre, so use ordinary auxiliary interpolation, ordinary derivative vanishing, and ordinary coordinate rigidity after proving the place/contact comparison. For m=1, the conclusion conflicts with generation and transcendence degree one, correctly ruling out excess.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_excess_forces_constant
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
    (hexcess :
      (R : Real) * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
        (1 + (sigma : Real)) *
          (∑ᶠ nu : PolynomialCurvePlace E,
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    ∃ i : Fin m, ∃ a : Complex, x i.succ = algebraMap Complex E a := by sorry
