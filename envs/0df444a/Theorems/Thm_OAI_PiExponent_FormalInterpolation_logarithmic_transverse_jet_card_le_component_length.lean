-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_jet_card_le_component_length
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_transverse_jet_card_le_component_length
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:40:40.794675+00:00
-- url     : https://prove2.me/theorems/11d0bf35-5708-425b-994b-ed32216f2bbd
-- title:
--   Independent logarithmic directions force local jet length
-- statement:
--   Vanishing of all frame words of cost strictly below T forces local quotient length to dominate the number of retained monomials in any independent family of logarithmic normal directions. Use the commuting-derivation Taylor map into the finite weighted jet algebra, cotangent surjectivity, and length monotonicity under a surjection. Minimality and finite source length are unnecessary. For empty B the retained constant gives the valid lower bound one, since the empty word ensures S is contained in P.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_transverse_jet_card_le_component_length
    {m : Nat} (v : Fin (m + 1) → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (B : Finset (Fin (m + 1)))
    (hB : LinearIndependent (logarithmicPrimeField P)
      (fun i : B => logarithmicNormalColumnAtPrime P i))
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word < T → logarithmicFrameWord word f ∈ P) :
    (strictWeightedSimplexCard (fun i : B => v i) T : ENat) ≤
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P := by
  sorry
