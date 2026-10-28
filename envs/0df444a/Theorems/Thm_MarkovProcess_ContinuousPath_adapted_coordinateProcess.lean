-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_adapted_coordinateProcess
-- name    : MarkovProcess.ContinuousPath.adapted_coordinateProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:27:22.976594+00:00
-- url     : https://prove2.me/theorems/fd281af4-a04b-46ac-b42a-7b4ac9e715fb
-- title:
--   Coordinate process is strongly adapted to its canonical filtration
-- statement:
--   The canonical coordinate process of continuous paths is strongly adapted to its filtration, because each time coordinate is measurable for the corresponding filtration sigma-algebra. This is the original, source-faithful theorem of Scott Armstrong (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/StoppedValueMeasurability.lean#L32-L36

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem MarkovProcess.ContinuousPath.adapted_coordinateProcess :
    StronglyAdapted (canonicalFiltration (alpha := alpha)) (coordinateProcess (alpha := alpha)) := by sorry
