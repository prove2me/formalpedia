-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:36:00.617039+00:00
-- url     : https://prove2.me/theorems/475a150a-1f80-4fc5-bd21-43424ecaddf3
-- title:
--   Separated centers give comaximal logarithmic ideals
-- statement:
--   For a coordinate injective on the center indices, the local logarithmic center ideals at any two distinct indices are comaximal. In the separating coordinate, the two logarithmic coordinate polynomials differ by the nonzero scalar difference of the center values. Powers of these coordinates still generate comaximal ideals by a finite binomial expansion; if the coordinate’s bound is zero, the corresponding ideal is already the whole ring.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwise_comaximal_of_separating_coordinate
    {m K : Nat} (T : Fin m → Nat) (S : Fin (m + 1) → Nat)
    (c : Fin K → Fin m → Complex) (i : Fin m)
    (hi : Function.Injective (fun j : Fin K => c j i)) :
    ∀ j k : Fin K, j ≠ k →
      logarithmicCenterIdeal (c j) T S ⊔ logarithmicCenterIdeal (c k) T S = ⊤ := by sorry
