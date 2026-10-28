-- Prove2me | Theorems.Thm_MarkovProcess_measurable_laplaceDensity
-- name    : MarkovProcess.measurable_laplaceDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:55:09.057775+00:00
-- url     : https://prove2.me/theorems/300c6a8e-e85a-41c0-a1f5-4b5eab036557
-- title:
--   Measurability of the exponential Laplace weight
-- statement:
--   For each real Laplace shift lam, the exponential density t ↦ ENNReal.ofReal (Real.exp (-lam * t)) is measurable. The original theorem and proof are from Scott Armstrong's MarkovProcess/Killed/GluingPotential.lean lines 47-51 at commit 1f8060caa137731fa08029592019eeaf9d997fe5, Apache-2.0.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem MarkovProcess.measurable_laplaceDensity (lam : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) := by sorry
