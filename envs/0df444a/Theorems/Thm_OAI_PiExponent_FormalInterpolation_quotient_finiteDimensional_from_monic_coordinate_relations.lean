-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_finiteDimensional_from_monic_coordinate_relations
-- name    : OAI.PiExponent.FormalInterpolation.quotient_finiteDimensional_from_monic_coordinate_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:26:18.928384+00:00
-- url     : https://prove2.me/theorems/ea9d2df2-0cc8-4eda-afe6-4fd7d5db9e72
-- title:
--   Monic coordinate relations imply a finite-dimensional polynomial quotient
-- statement:
--   If every variable class in the quotient is annihilated by a monic polynomial over Complex, then the quotient is finite-dimensional over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.quotient_finiteDimensional_from_monic_coordinate_relations
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hrel : ∀ i : Fin (m + 1),
      ∃ p : Polynomial Complex,
        p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0) :
    FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := by sorry
