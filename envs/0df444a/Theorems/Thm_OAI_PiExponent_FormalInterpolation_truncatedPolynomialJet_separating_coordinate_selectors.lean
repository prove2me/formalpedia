-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_separating_coordinate_selectors
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_separating_coordinate_selectors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:17:01.874383+00:00
-- url     : https://prove2.me/theorems/87bc3a37-ab62-4a22-b2a3-ccad74b66fa8
-- title:
--   Local jet selectors from coordinate separation
-- statement:
--   Construct polynomial selectors whose truncated jet coefficients on the finite exponent box equal those of the constant 1 at the selected center and vanish at all other centers. The proof route is to identify the box with reduction modulo a monomial ideal, pull those ideals back through the triangular substitutions, establish pairwise comaximality using the separating coordinate, and apply finite CRT.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_separating_coordinate_selectors
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (hsep : K = 0 ∨ ∃ i : Fin m, Function.Injective (fun j : Fin K => c j i)) :
    ∃ E : Fin K → MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j k : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T (E k)).coeff
            (InterpolationMatrix.exponentVector a.1) =
          if j = k ∧ a.1 = 0 then 1 else 0 := by sorry
