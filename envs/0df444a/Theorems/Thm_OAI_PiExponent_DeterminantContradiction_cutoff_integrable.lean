-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_cutoff_integrable
-- name    : OAI.PiExponent.DeterminantContradiction.cutoff_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:50:36.567698+00:00
-- url     : https://prove2.me/theorems/9f4597b2-99a6-468f-a8ad-e4d08565caca
-- title:
--   Integrability of the simplex power cutoff
-- statement:
--   The cutoff power function is integrable over the real line because it is measurable, bounded on its bounded support `[0,T)`, and zero outside that support. This includes `m = 0`; the strict upper cutoff excludes `T` and does not affect integrability.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.cutoff_integrable (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.Integrable (fun t : Real =>
      if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0) MeasureTheory.volume := by sorry
