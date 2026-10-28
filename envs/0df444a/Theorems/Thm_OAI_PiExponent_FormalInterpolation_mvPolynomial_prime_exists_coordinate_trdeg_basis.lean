-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_prime_exists_coordinate_trdeg_basis
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_exists_coordinate_trdeg_basis
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:44:21.616138+00:00
-- url     : https://prove2.me/theorems/8456f846-91cb-4b94-b08d-347afa626d59
-- title:
--   A coordinate transcendence basis for the prime quotient field
-- statement:
--   For a prime ideal in a finite-variable polynomial ring over Complex, a subset of the coordinate images in the quotient fraction field is algebraically independent and has cardinality equal to the transcendence degree.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_prime_exists_coordinate_trdeg_basis
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ∃ s : Finset (Fin (m + 1)),
      AlgebraicIndependent Complex
        (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (logarithmicPrimeField P) (MvPolynomial.X i.1)) ∧
      s.card = (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
  sorry
