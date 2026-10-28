-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_progMeasurable_coordinateProcess
-- name    : MarkovProcess.ContinuousPath.progMeasurable_coordinateProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:45:58.981325+00:00
-- url     : https://prove2.me/theorems/c6236a38-eb7e-4f12-bc01-31dbc90b0a25
-- title:
--   Continuous coordinate process is progressively measurable
-- statement:
--   A strongly adapted canonical coordinate process with continuous sample paths is strongly progressively measurable. This is the original, source-faithful theorem of Scott Armstrong (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/StoppedValueMeasurability.lean#L37-L42

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
import Theorems.Thm_MarkovProcess_ContinuousPath_adapted_coordinateProcess
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem MarkovProcess.ContinuousPath.progMeasurable_coordinateProcess :
    IsStronglyProgressive (canonicalFiltration (alpha := alpha))
      (coordinateProcess (alpha := alpha)) := by sorry
