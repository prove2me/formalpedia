-- Prove2me | Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_unitDyadicGridBadIncrement_le
-- name    : MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:10:09.002037+00:00
-- url     : https://prove2.me/theorems/f3e4c2d5-ce6d-4a67-87ea-1fc07da49cbf
-- title:
--   Kolmogorov finite-grid bound for adjacent unit dyadic increments
-- statement:
--   The probability of a large increment on a level-n unit dyadic grid is controlled by the number of grid intervals times the Kolmogorov moment bound at the dyadic mesh scale. This theorem is the original result of Scott Armstrong, MarkovProcess, Apache-2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteGridIncrement.lean#L83-L92

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_finiteGridBadIncrement_le
import Theorems.Thm_MarkovProcess_unitDyadicGrid_edist_adjacent_le
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (n : ℕ) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p ε) ≤
      2 ^ n * (M * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q / ε ^ p) := by sorry
