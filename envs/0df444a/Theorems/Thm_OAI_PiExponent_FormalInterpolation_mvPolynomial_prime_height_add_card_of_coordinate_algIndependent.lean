-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:52:31.107567+00:00
-- url     : https://prove2.me/theorems/cc914588-f0c8-4bea-b38b-eb308047a3a9
-- title:
--   Height bound from a coordinate transcendence basis
-- statement:
--   For a prime ideal in this finite-coordinate polynomial ring, an algebraically independent subset of coordinate images whose cardinality equals the quotient fraction field’s transcendence degree gives the height bound on the number of coordinates.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_height_add_card_of_coordinate_algIndependent
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i.1)))
    (hcard : s.card =
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) :
    m + 1 ≤ P.height + s.card := by
  sorry
