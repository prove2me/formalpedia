-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_relations_of_finiteDimensional_each
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_relations_of_finiteDimensional_each
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:36:41.957493+00:00
-- url     : https://prove2.me/theorems/1f157400-9abd-4d61-82a2-be97fac6f590
-- title:
--   Finite-dimensional polynomial quotients give individual coordinate relations
-- statement:
--   For every coordinate, finite-dimensionality of the quotient gives a monic polynomial relation of some positive degree, represented by coefficients below that degree.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_relations_of_finiteDimensional_each
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J)) :
    ∀ i : Fin (m + 1), ∃ n : Nat, 0 < n ∧ ∃ c : Fin n → Complex,
      MvPolynomial.X i ^ n -
        ∑ k : Fin n, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J := by sorry
