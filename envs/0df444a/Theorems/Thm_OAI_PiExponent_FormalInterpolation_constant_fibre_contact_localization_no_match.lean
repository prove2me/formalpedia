-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_no_match
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_no_match
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T03:52:44.574982+00:00
-- url     : https://prove2.me/theorems/13827655-bb5a-4891-a2b5-3c189af2accf
-- title:
--   Zero contact when no center matches the constant coordinate
-- statement:
--   Under the no-match hypothesis, the product of the `i0`-coordinate generators, one from each center ideal, evaluates to a nonzero constant. Its ideal membership forces zero contact at affine places, while contact is zero by definition elsewhere. This isolates the no-match branch; its proof still requires constructing the product-ideal element and relating its order to the contact infimum. An independent route is to prove generator evaluation from `hfibre`, show the finite product belongs to `logarithmicCentersIdeal`, then use the definition of `polynomialCurveIdealContact` place by place. The empty product handles `K = 0`; zero exponents give unit generators.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_no_match
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (hn : ∀ j : Fin K, c j i0 ≠ a) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) = 0 := by sorry
