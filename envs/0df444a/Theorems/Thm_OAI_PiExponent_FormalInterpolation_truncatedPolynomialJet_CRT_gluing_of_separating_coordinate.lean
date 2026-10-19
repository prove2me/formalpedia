-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T18:41:12.0044+00:00
-- url     : https://prove2.me/theorems/c76b42d2-6e88-44e7-9417-7d3e3690c020
-- title:
--   CRT gluing for jets at coordinate-separated centers
-- statement:
--   For any finite family of centers in complex coordinate space, one polynomial matches the prescribed truncated jet coefficients on the given finite exponent box when the family is empty or some coordinate separates all centers.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing_of_separating_coordinate
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hsep : K = 0 ∨ ∃ i : Fin m, Function.Injective (fun j : Fin K => c j i)) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (c j) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by sorry
