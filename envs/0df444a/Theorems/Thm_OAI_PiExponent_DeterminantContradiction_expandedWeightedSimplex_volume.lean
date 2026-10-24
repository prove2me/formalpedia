-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_expandedWeightedSimplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.expandedWeightedSimplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:01:41.397083+00:00
-- url     : https://prove2.me/theorems/529fba51-f048-4a0d-b331-94728146ff24
-- title:
--   Volume of the expanded weighted simplex
-- statement:
--   The expanded closed weighted simplex has the standard simplex volume, expressed as an ENNReal.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.expandedWeightedSimplex_volume
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} =
      ENNReal.ofReal
        ((H + Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) := by sorry
