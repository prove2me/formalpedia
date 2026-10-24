-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_arithmetic
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_arithmetic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:14:43.821081+00:00
-- url     : https://prove2.me/theorems/af0f556c-c812-4117-81ce-c22e294fe06e
-- title:
--   Simplify the scaled simplex volume factor
-- statement:
--   For positive weights and positive B, the reciprocal diagonal factors times 1/n! simplify to Bⁿ divided by n! times the product of the weights. Prove the real identity by finite-product algebra, then use the ENNReal ofReal multiplication rules.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_arithmetic
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (B : Real) (hB : 0 < B) :
    (∏ i, ENNReal.ofReal (1 / (w i / B))) *
        ENNReal.ofReal (1 / (n.factorial : Real)) =
      ENNReal.ofReal
        (B ^ n / ((n.factorial : Real) * Finset.univ.prod w)) := by sorry
