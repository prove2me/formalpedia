-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_jet_contact_bound
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_jet_contact_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T08:42:52.694707+00:00
-- url     : https://prove2.me/theorems/41805cde-bad3-4b2b-bac3-c62b16a47a81
-- title:
--   Weighted logarithmic jets force curve contact
-- statement:
--   For the stated generating tuple in a one-variable function field, a polynomial with weighted formal jets vanishing below H has curve order at least H times its positive contact with the canonical center ideal, divided by R. The strict cutoff remains exactly `e 0`; the scaling hypothesis is required coordinatewise. The independent proof must connect the formal-jet coefficient conditions to valuations at the branch and account for contact with the product ideal.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_jet_contact_bound
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
    (nu : PolynomialCurvePlace E)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))
    (hne : MvPolynomial.aeval x G ≠ 0) :
    H * (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) ≤
      (R : Real) * (polynomialCurveOrder nu (MvPolynomial.aeval x G) : Real) := by sorry
