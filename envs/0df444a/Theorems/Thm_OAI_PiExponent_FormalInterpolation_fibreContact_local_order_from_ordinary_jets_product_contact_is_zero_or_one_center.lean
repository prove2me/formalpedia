-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:40:41.12198+00:00
-- url     : https://prove2.me/theorems/3f1c9983-d74c-491d-8e72-8aef1dc32256
-- title:
--   Distinct centers isolate positive product contact
-- statement:
--   The contact of the product of all logarithmic center ideals is either zero or is exactly the contact at one center. Injectivity of each coordinate’s center map means two distinct centers cannot both have all coordinate differences of positive valuation at an integral place; otherwise subtracting the differences would give a nonzero constant of positive valuation. Product-ideal valuations then reduce contact to the sole potentially positive center. If K is zero, m is zero, or the place is non-affine, the zero-contact branch applies. A proof route is to characterize contact through the finite powered generators, use the valuation inequality on differences to prove uniqueness of a positive-contact center, and establish additivity for the product ideal. The remaining obligation is this ideal-contact characterization and product calculation, including the zero cases.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (f : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) f)
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0) :
    polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) = 0 ∨
    ∃ j : Fin K,
      polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) =
      polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) := by sorry
