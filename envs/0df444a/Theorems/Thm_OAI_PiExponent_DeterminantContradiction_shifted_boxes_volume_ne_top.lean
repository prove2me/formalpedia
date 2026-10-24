-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_shifted_boxes_volume_ne_top
-- name    : OAI.PiExponent.DeterminantContradiction.shifted_boxes_volume_ne_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:54:26.530201+00:00
-- url     : https://prove2.me/theorems/d56a4465-13f8-4ae9-bc62-0d39ab4ba343
-- title:
--   The finite union of shifted unit boxes has finite volume
-- statement:
--   The box union has finite volume because its index set is finite and each box is a bounded unit box in finite-dimensional real space. This supplies the finiteness premise for the parent's toReal comparison. A proof route is to bound each box's Lebesgue measure and use the finite-union measure bound; the empty-dimensional case also has finite volume.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.shifted_boxes_volume_ne_top
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
        {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) ≠ ⊤ := by sorry
