-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_constant_fibre_contact_le
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicIdeal_constant_fibre_contact_le
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-20T22:34:27.821259+00:00
-- url     : https://prove2.me/theorems/1fb61158-4f5e-4a33-9609-0011d88fc578
-- title:
--   Product-formula contact bound for a unit-fibre curve with a constant coordinate
-- statement:
--   For arbitrary truncation orders, a generating curve on x₀=1 with a constant positive-index coordinate satisfies the weighted contact bound whenever eᵢwᵢ≤ρ for every positive index. Coordinatewise injectivity selects at most one contributing center. Bound its contact by a transcendental coordinate's vanishing divisor and apply the product formula and weighted pole bound. An unmatched constant gives zero contact. Empty center families and zero contact are harmless; the existence of a constant coordinate together with a generating transcendental curve excludes the dimension-zero case.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicIdeal_constant_fibre_contact_le
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (w : Fin (m + 1) → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Real) (hrho : 0 ≤ rho)
    (hcoeff : ∀ i : Fin m, (e i.succ : Real) * (w i.succ : Real) ≤ rho)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hconstant : ∃ i : Fin m, ∃ a : Complex,
      x i.succ = algebraMap Complex E a) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
      rho * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by sorry
