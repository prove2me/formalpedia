-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_jet_bound_controls_center_contact
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_jet_bound_controls_center_contact
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:15:43.759072+00:00
-- url     : https://prove2.me/theorems/ce6ef618-3760-4c19-8b48-4fc1bbca7682
-- title:
--   Weighted logarithmic jets bound local curve order
-- statement:
--   For one center, the weighted formal-jet vanishing condition bounds the curve order of the nonzero evaluated polynomial by the center contact and the scale `R`. This removes the formal-series and valuation estimate from the parent. A proof route is to evaluate the formal jet in the local valuation ring, bound each surviving monomial using the logarithmic coordinate orders, and use `R = e i * v i` coordinatewise; the strict cutoff permits terms exactly at weight `H`. The truncated logarithm contribution must be controlled at its exact cutoff `e 0`, which is the remaining core obligation.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_jet_bound_controls_center_contact
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (H : Real) (G : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H G)
    (nu : PolynomialCurvePlace E) (j : Fin K)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real))
    (hne : MvPolynomial.aeval x G ≠ 0) :
    H * (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ≤
      (R : Real) * (polynomialCurveOrder nu (MvPolynomial.aeval x G) : Real) := by sorry
