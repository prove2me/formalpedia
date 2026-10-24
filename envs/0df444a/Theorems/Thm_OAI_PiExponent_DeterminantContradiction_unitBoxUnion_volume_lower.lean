-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitBoxUnion_volume_lower
-- name    : OAI.PiExponent.DeterminantContradiction.unitBoxUnion_volume_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:11:12.50559+00:00
-- url     : https://prove2.me/theorems/673484cd-21fe-45b7-b4d1-739e72b15acd
-- title:
--   Finite unions of integer unit boxes have volume at least their count
-- statement:
--   For any finite set of integer vectors, the union of their translated half-open unit boxes has volume at least the number of vectors.

import Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.unitBoxUnion_volume_lower
    {n : ℕ} (S : Finset (Fin n → ℕ)) :
    ENNReal.ofReal (S.card : ℝ) ≤ MeasureTheory.volume (unitBoxUnion S) := by sorry
