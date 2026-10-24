-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:20:17.084634+00:00
-- url     : https://prove2.me/theorems/f9a7aa3c-301a-4b51-b97e-34b5f971efab
-- title:
--   Scaling a positive-size simplex
-- statement:
--   Positive scalar dilation maps the T-simplex to the s-simplex and scales volume by (s/T)^m. This removes the slice-rescaling step from the parent. Prove by the change-of-variables formula for dilation. Both size parameters are positive; in particular, s > 0 is needed in dimension zero because the strict sum bound makes the zero-dimensional set empty at size zero.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_scale (m : Nat) (s T : Real) (hs : 0 < s) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin m → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s} =
      ENNReal.ofReal ((s / T) ^ m) *
        MeasureTheory.volume {x : Fin m → Real |
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by sorry
