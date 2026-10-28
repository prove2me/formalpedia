-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_height_add_card_of_coordinate_transcendence_basis
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_card_of_coordinate_transcendence_basis
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T01:05:53.46581+00:00
-- url     : https://prove2.me/theorems/4be86b2a-c368-4b2f-a372-ed24eb703e4c
-- title:
--   Height bound from a coordinate transcendence basis
-- statement:
--   For a prime ideal in the finite-variable polynomial ring, the height plus the cardinality of a coordinate transcendence basis of the quotient’s fraction field is at least the number of variables. This isolates the height and dimension argument from the separate task of finding that basis.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_card_of_coordinate_transcendence_basis
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))
        (MvPolynomial.X i.1)))
    (hcard : s.card =
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat) :
    m + 1 ≤ P.height + s.card := by sorry
