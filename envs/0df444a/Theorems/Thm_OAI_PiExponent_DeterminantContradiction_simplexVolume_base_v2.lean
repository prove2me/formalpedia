-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_base_v2
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_base_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:02:37.090982+00:00
-- url     : https://prove2.me/theorems/285d442e-b3cb-4e19-b918-ba7ae9be3e98
-- title:
--   Zero dimensional unit simplex volume
-- statement:
--   The unit coordinate simplex in dimension zero has volume one.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_base_v2 :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by sorry
