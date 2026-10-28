-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:36:57.729611+00:00
-- url     : https://prove2.me/theorems/dfe57d69-bd8a-4bb2-b027-d5aac3d5b3d5
-- title:
--   Persistent logarithmic jets force local length
-- statement:
--   The hwords hypothesis forces every logarithmic jet below the strict cutoff to vanish on the component. The independent logarithmic normal directions and hY give transverse flow coordinates, so the local quotient length dominates the count of retained weighted monomials. This isolates the flow-coordinate and lower-length argument from the parent. When B is empty, the strict simplex still contains its zero exponent because T is positive.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_transverse_simplex_card_le_component_local_length_from_multiplicity
    {m : Nat} (v : Fin (m + 1) → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (B : Finset (Fin (m + 1)) )
    (hB : LinearIndependent (logarithmicPrimeField P)
      (fun i : B => logarithmicNormalColumnAtPrime P i))
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word < T → logarithmicFrameWord word f ∈ P) :
    (strictWeightedSimplexCard (fun i : B => v i) T : ENat) ≤
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P := by
  sorry
