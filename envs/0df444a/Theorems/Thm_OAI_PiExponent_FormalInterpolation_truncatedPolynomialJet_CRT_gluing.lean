-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_CRT_gluing
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:12:12.412773+00:00
-- url     : https://prove2.me/theorems/da36d4b0-7245-495c-96e2-560bb9044c1c
-- title:
--   Simultaneous realization at distinct centers
-- statement:
--   One polynomial can match given local jet coefficients from every center `j * r` throughout a finite box. The lemma isolates the CRT step from the construction of each local polynomial and from the row-weight estimate. A proof route identifies each triangular substitution with local coordinates, shows the coordinate-power ideals for distinct centers are comaximal using a nonzero coordinate of `r`, and applies the finite CRT. Empty center or box cases are included.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_CRT_gluing
    {m : Nat} (K : Nat) (T : Fin m → Nat) (r : Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hr : ∃ i, r i ≠ 0) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (fun i => (j.val : Complex) * r i) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (fun i => (j.val : Complex) * r i) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by sorry
