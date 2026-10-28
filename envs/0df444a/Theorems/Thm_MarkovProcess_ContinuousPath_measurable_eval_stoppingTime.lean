-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_measurable_eval_stoppingTime
-- name    : MarkovProcess.ContinuousPath.measurable_eval_stoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:53:33.224305+00:00
-- url     : https://prove2.me/theorems/c6bd1029-0082-4a86-9cfb-71c754d61796
-- title:
--   Evaluation at a finite stopping time is measurable for the stopped sigma-algebra
-- statement:
--   For a stopping-time map into finite nonnegative time, the continuous-path coordinate evaluated at that random time is measurable for the stopped measurable structure. This is the original, source-faithful theorem of Scott Armstrong (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/StoppedValueMeasurability.lean#L43-L49

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
import Theorems.Thm_MarkovProcess_ContinuousPath_adapted_coordinateProcess
import Theorems.Thm_MarkovProcess_ContinuousPath_progMeasurable_coordinateProcess
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem MarkovProcess.ContinuousPath.measurable_eval_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable[hT.measurableSpace] (fun omega ↦ omega (T omega)) := by sorry
