-- Prove2me | Theorems.Thm_MarkovProcess_unitDyadicGrid_edist_adjacent_le
-- name    : MarkovProcess.unitDyadicGrid_edist_adjacent_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:03:46.695063+00:00
-- url     : https://prove2.me/theorems/6f872708-12f5-4614-957f-4c67d2341db3
-- title:
--   Bound the spacing of adjacent unit dyadic grid points
-- statement:
--   Consecutive rational points on the level-n unit dyadic grid have extended distance at most the inverse of two to the nth power. This theorem is the original result of Scott Armstrong, MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteGridIncrement.lean#L69-L82

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.unitDyadicGrid_edist_adjacent_le (n : ℕ) (i : Fin (2 ^ n)) :
    edist (unitDyadicGrid n i.castSucc) (unitDyadicGrid n i.succ) ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by sorry
