-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_variables_integral_of_finiteDimensional
-- name    : OAI.PiExponent.FormalInterpolation.variables_integral_of_finiteDimensional
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:15:52.880517+00:00
-- url     : https://prove2.me/theorems/5c7bc3a4-10d1-4d54-b6e5-d7cc25894c60
-- title:
--   Variable classes are integral in finite-dimensional polynomial quotients
-- statement:
--   In a finite-dimensional quotient of the multivariate polynomial ring, the class of each variable is integral over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.variables_integral_of_finiteDimensional
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i)) := by sorry
