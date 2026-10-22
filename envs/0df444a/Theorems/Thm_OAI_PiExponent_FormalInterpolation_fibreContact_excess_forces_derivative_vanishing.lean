-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_excess_forces_derivative_vanishing
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_excess_forces_derivative_vanishing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:44:22.974333+00:00
-- url     : https://prove2.me/theorems/2abd7dd5-b76e-42d0-beb8-e4bfad44ac52
-- title:
--   Excess fibre contact annihilates low-cost ordinary derivatives
-- statement:
--   An auxiliary polynomial with jet threshold (1+3 sigma)N has every derivative of cost at most sigma N vanish on a curve with excess ideal contact. Prove the exact local contact formula using the fibre restriction and R=e_i v_i, establish finite support, and compare zero and pole divisors. This child requires neither volume nor weight separation.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_excess_forces_derivative_vanishing
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound (fun i => w i.succ) N F)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (hexcess :
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    ∀ word : List (Fin m),
      fibreContactWordCost (fun i => v i.succ) word ≤ (sigma : Real) * (N : Real) →
        MvPolynomial.aeval (fun i => x i.succ) (fibreContactWord word F) = 0 := by sorry
