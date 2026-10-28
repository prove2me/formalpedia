-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_word_ideal_contact_estimates
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_word_ideal_contact_estimates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T03:41:55.65046+00:00
-- url     : https://prove2.me/theorems/e957da7d-7ac6-44a1-857f-2182088787fc
-- title:
--   Logarithmic words preserve degree and retain scaled ideal contact
-- statement:
--   A word of logarithmic frame derivatives does not increase weighted degree. At a branch with positive canonical ideal contact, its finite vanishing order is at least the retained jet weight M minus word cost, times ideal contact divided by R. The ideal uses precisely the strict cutoff e 0.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_word_ideal_contact_estimates
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (w v : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (N M : Real) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hjet : logarithmicJetBound c v M F)
    (word : List (Fin (m + 1))) (hword : logarithmicFrameCost v word ≤ M) :
    logarithmicDegreeBound w N (logarithmicFrameWord word F) ∧
      ∀ nu : PolynomialCurvePlace E,
        0 < (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) →
        MvPolynomial.aeval x (logarithmicFrameWord word F) ≠ 0 →
        (M - logarithmicFrameCost v word) *
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) ≤
          (R : Real) * (polynomialCurveOrder nu
            (MvPolynomial.aeval x (logarithmicFrameWord word F)) : Real) := by sorry
