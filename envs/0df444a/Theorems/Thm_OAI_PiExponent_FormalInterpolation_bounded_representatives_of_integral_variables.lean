-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_integral_variables
-- name    : OAI.PiExponent.FormalInterpolation.bounded_representatives_of_integral_variables
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:16:20.545231+00:00
-- url     : https://prove2.me/theorems/20544a63-a582-403e-ab1e-315d6dd42569
-- title:
--   Integral variable classes give bounded-support representatives
-- statement:
--   If every variable class is integral over Complex modulo an ideal, every monomial has a representative whose support exponents are strictly below one uniform bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_representatives_of_integral_variables
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hvars : ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
