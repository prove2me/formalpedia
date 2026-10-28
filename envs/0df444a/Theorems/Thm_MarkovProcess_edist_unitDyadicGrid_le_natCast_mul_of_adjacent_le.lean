-- Prove2me | Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
-- name    : MarkovProcess.edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:49:21.903099+00:00
-- url     : https://prove2.me/theorems/2dc1d66c-0baa-4cb6-884e-5958051fe9a1
-- title:
--   Dyadic grid increments bounded by adjacent increments
-- statement:
--   Uniform control of adjacent increments on one unit dyadic grid controls the increment
--   between any two ordered grid points by the number of intervening cells.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicChaining.lean#L29-L56

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    (i j : Fin (2 ^ n + 1)) (hij : (i : ℕ) ≤ j) :
    edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
      (j.val - i.val : ℕ) * ε := by sorry
