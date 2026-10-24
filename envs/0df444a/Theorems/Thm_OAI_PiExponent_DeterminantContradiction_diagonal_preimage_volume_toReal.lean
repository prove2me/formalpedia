-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_preimage_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:52:38.078987+00:00
-- url     : https://prove2.me/theorems/6c9fae13-dff5-4c45-816c-3ffc65c465d2
-- title:
--   Diagonal preimage volume scaling
-- statement:
--   For positive coordinate scales, the volume of the preimage of a compact set under the diagonal map is its volume divided by the product of the scales.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume_toReal {m : Nat} (w : Fin m → Real) (hw : ∀ i, 0 < w i) (s : Set (Fin m → Real)) (hs : IsCompact s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) ⁻¹' s)).toReal =
      (MeasureTheory.volume s).toReal / ∏ i : Fin m, w i := by sorry
