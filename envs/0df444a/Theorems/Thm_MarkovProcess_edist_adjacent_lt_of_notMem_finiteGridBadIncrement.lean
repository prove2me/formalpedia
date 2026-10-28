-- Prove2me | Theorems.Thm_MarkovProcess_edist_adjacent_lt_of_notMem_finiteGridBadIncrement
-- name    : MarkovProcess.edist_adjacent_lt_of_notMem_finiteGridBadIncrement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:15:02.493258+00:00
-- url     : https://prove2.me/theorems/8c9fdc97-56bf-4123-bfda-7e81a51c1da8
-- title:
--   Avoiding the finite-grid bad event bounds every adjacent increment
-- statement:
--   Outside the bad-increment event of a finite grid, each adjacent increment has extended distance strictly below its specified threshold, provided the moment exponent is positive.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicIncrements.lean#L166-L174

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.edist_adjacent_lt_of_notMem_finiteGridBadIncrement
    {N : ℕ} {T : Type*} {X : T → Ω → E} {grid : Fin (N + 1) → T}
    {p : ℝ} (hp : 0 < p) {ε : ℝ≥0∞} {ω : Ω}
    (hω : ω ∉ finiteGridBadIncrement X grid p ε) (i : Fin N) :
    edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) < ε := by sorry
