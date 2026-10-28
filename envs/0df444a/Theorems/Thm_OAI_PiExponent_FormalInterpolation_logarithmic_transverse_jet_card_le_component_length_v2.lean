-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_jet_card_le_component_length_v2
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_transverse_jet_card_le_component_length_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T08:47:29.230984+00:00
-- url     : https://prove2.me/theorems/77da723b-57e9-4823-842b-95bb7a6c13c6
-- title:
--   Independent logarithmic directions force local jet length
-- statement:
--   For any selected independent family of logarithmic normal columns, vanishing of all frame words of cost strictly below `T` makes the local quotient length dominate the number of retained exponent vectors. Since `T > 0`, the empty word is included, so the equations lie in `P`; for empty `B`, the counted constant vector gives the lower bound one. A proof route constructs the weighted jet map from the localized quotient, uses independence of the normal columns for the transverse directions, and applies length monotonicity to the finite jet quotient. This removes the jet-count comparison from the parent; constructing and proving surjectivity of that map remain the core obligations.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_transverse_jet_card_le_component_length_v2
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
