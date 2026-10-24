-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_word_jets
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_word_jets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:29:52.782106+00:00
-- url     : https://prove2.me/theorems/0013319c-2d17-4533-93aa-66aac1dc64fd
-- title:
--   Word jet vanishing controls local logarithmic ideal contact
-- statement:
--   Under the target’s curve-field, fibre, positivity, and scale hypotheses, vanishing of the derivative word’s translated coefficients below `(1+2σ)N` implies the claimed local order lower bound against the logarithmic-centers ideal. The nonzero evaluation hypothesis ensures the evaluated function has a finite order to compare. This is the remaining geometric core of the target.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_word_jets
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
    (N : Nat) (hN : 0 < N) (F : MvPolynomial (Fin m) Complex)
    (word : List (Fin m))
    (hwordJet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) (fibreContactWord word F))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F) ≠ 0) :
    ((polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) *
      ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu
          (MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F)) : Real) := by sorry
