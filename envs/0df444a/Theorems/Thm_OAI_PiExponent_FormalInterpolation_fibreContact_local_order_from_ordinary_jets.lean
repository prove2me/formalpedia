-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:34:29.593302+00:00
-- url     : https://prove2.me/theorems/e2de616d-ed21-44cf-8dc5-b1995f9c25fa
-- title:
--   Ordinary weighted jets bound logarithmic ideal contact
-- statement:
--   For any polynomial whose translated coefficients at every center vanish below the specified positive weighted jet cutoff, prove the stated bound between its evaluated order at a curve place and the contact of the product logarithmic-center ideal. The child keeps the original curve-field, fibre, nonconstancy, and scale hypotheses. Its new argument is the general weighted-jet-to-contact estimate; the parent removes only the derivative-word specialization. A proof route is to turn the coefficient vanishing into weighted local order bounds at each center, compare those bounds with the valuations of the logarithmic-coordinate generators, and combine the comparisons using the product ideal and the normalized place. The missing core is precisely that local-to-ideal contact comparison with the stated quantitative factor.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets
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
    ((polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by sorry
