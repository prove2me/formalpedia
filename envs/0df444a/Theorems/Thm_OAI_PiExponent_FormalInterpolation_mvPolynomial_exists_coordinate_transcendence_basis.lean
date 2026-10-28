-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T01:05:03.018655+00:00
-- url     : https://prove2.me/theorems/8a1ba15c-da27-4e42-beee-1d004dac2ec1
-- title:
--   A coordinate transcendence basis exists
-- statement:
--   The images of the finitely many coordinate variables generate the quotient’s fraction field over the complex numbers. A maximal algebraically independent subset of those coordinates is therefore a transcendence basis, and its cardinality is the quotient field’s transcendence degree.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ∃ s : Finset (Fin (m + 1)),
      AlgebraicIndependent Complex
        (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))
          (MvPolynomial.X i.1)) ∧
      s.card =
        (Algebra.trdeg Complex
          (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by sorry
