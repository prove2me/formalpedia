-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_explicitBounds_power_integral
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_power_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:57:31.883702+00:00
-- url     : https://prove2.me/theorems/3857d46a-2be6-4110-95b8-bf16420d8eef
-- title:
--   Integral of the explicit simplex power
-- statement:
--   The integral of the normalized `m`th power of the remaining cutoff equals the normalized `(m + 1)`st power. Evaluate the power integral on `[0,A]` and simplify with the factorial successor identity; `A = 0` gives zero on both sides. This removes the calculus and factorial algebra from the induction step.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_power_integral (m : Nat) (A : Real) (hA : 0 ≤ A) :
    ∫ t in Set.Icc (0 : Real) A, (A - t) ^ m / ((Nat.factorial m : Nat) : Real) =
      A ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by sorry
