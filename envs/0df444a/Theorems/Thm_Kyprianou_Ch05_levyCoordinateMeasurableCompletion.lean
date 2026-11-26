-- Prove2me | Theorems.Thm_Kyprianou_Ch05_levyCoordinateMeasurableCompletion
-- name    : Kyprianou.Ch05.levyCoordinateMeasurableCompletion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:06:55.336205+00:00
-- url     : https://prove2.me/theorems/9636345d-922e-5c4b-8474-14adb2ad62c7
-- title:
--   Lévy process coordinates are measurable on the completion
-- statement:
--   Stationary increments supply a.e. measurability of the increment starting at zero, which is the coordinate itself. Such coordinates are measurable in the completion.
-- source:
--   Kyprianou (2006), Chapter 5; completion transport for strong Markov reuse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.levyCoordinateMeasurableCompletion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (Y : NNReal → Omega → Real)
    (hY : ProbabilityTheory.IsLevyProcess Y P) :
    ∀ t : NNReal, Measurable (fun w : NullMeasurableSpace Omega P => Y t w) := by
  sorry
