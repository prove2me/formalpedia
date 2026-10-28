-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_survivalSet_top
-- name    : MarkovProcess.ContinuousPath.survivalSet_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:02:19.753558+00:00
-- url     : https://prove2.me/theorems/008d737a-a246-419b-b080-45432c694064
-- title:
--   Positive survival times under an infinite horizon
-- statement:
--   For the infinite ENNReal horizon, the set of strictly positive real times whose NNReal image is below the horizon is precisely the positive real half-line. Scott Armstrong's original statement and proof from MarkovProcess/Path/ExitTime.lean lines 42-47, pinned commit 1f8060caa137731fa08029592019eeaf9d997fe5, Apache-2.0.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

theorem MarkovProcess.ContinuousPath.survivalSet_top :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by sorry
