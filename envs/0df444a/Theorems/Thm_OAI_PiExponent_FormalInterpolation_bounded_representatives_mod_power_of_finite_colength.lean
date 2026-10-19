-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_mod_power_of_finite_colength
-- name    : OAI.PiExponent.FormalInterpolation.bounded_representatives_mod_power_of_finite_colength
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:02:28.496903+00:00
-- url     : https://prove2.me/theorems/6becfa4c-8b68-49b5-96e0-3d4d2765c8a3
-- title:
--   Bounded representatives modulo a power of a finite colength ideal
-- statement:
--   If the quotient of a multivariate complex polynomial ring by an ideal is finite-dimensional, then for every positive power of that ideal there is a uniform weighted-degree bound such that every polynomial has a representative below that bound modulo the power.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_representatives_mod_power_of_finite_colength
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (s : Nat) (hs : 0 < s) :
    ∃ C : Real, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s := by sorry
