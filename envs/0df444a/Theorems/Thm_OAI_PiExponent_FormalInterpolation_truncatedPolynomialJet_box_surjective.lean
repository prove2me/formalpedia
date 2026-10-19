-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_box_surjective
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_box_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:11:43.233778+00:00
-- url     : https://prove2.me/theorems/452e2928-a253-440b-abb6-859b9b2dd650
-- title:
--   One-center realization of a finite coefficient box
-- statement:
--   At one center, the triangular polynomial substitution can realize any prescribed coefficients on a finite coordinate box. This isolates local realization from both the weighted row bound and gluing. A proof can form the polynomial with the desired box coefficients and pull it back through the inverse triangular substitution. The statement includes zero side lengths, where the box is empty.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_box_surjective
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (S : Fin (m + 1) → Nat)
    (g : {a : Fin (m + 1) → Nat // ∀ i, a i < S i} → Complex) :
    ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
      ∀ a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i},
        (truncatedPolynomialJet c T Q).coeff
          (InterpolationMatrix.exponentVector a.1) = g a := by sorry
