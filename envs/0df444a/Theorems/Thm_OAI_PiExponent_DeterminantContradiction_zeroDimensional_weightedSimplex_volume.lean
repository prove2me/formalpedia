-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_zeroDimensional_weightedSimplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.zeroDimensional_weightedSimplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:58:52.299692+00:00
-- url     : https://prove2.me/theorems/3e791fa7-721a-47f3-b260-c315794d0e37
-- title:
--   Zero dimensional weighted simplex volume
-- statement:
--   In dimension zero the domain is a singleton, and the empty product and 0! are one, so both sides equal one, including when H = 0. This handles the case where the positive scaling bound used in the other children is unavailable.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.zeroDimensional_weightedSimplex_volume
    (w : Fin 0 → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} =
      ENNReal.ofReal
        ((H + Finset.univ.sum w) ^ 0 /
          ((Nat.factorial 0 : Real) * Finset.univ.prod w)) := by sorry
