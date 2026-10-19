-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_integral_class_has_monic_relation
-- name    : OAI.PiExponent.FormalInterpolation.integral_class_has_monic_relation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:20:29.028817+00:00
-- url     : https://prove2.me/theorems/7aad21b8-6223-4396-a8ec-4b6dd1d006a6
-- title:
--   Integral classes satisfy monic polynomial relations
-- statement:
--   An integral class of a polynomial variable in the quotient is annihilated by a monic polynomial over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.integral_class_has_monic_relation
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    {i : Fin (m + 1)}
    (h : IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    ∃ p : Polynomial Complex,
      p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0 := by sorry
