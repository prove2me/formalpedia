-- Prove2me | Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_child_parent_le_of_adjacent_le
-- name    : MarkovProcess.edist_unitDyadicGrid_child_parent_le_of_adjacent_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:17:10.994338+00:00
-- url     : https://prove2.me/theorems/9e885d16-004b-4200-b843-1a9d1ab8c649
-- title:
--   Adjacent-increment control on level `n + 1` controls every child-to-parent increment by the same threshold
-- statement:
--   Adjacent-increment control on level `n + 1` controls every child-to-parent increment
--   by the same threshold.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicChaining.lean#L141-L166

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







open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.edist_unitDyadicGrid_child_parent_le_of_adjacent_le
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ (n + 1)),
      edist (X (unitDyadicGrid (n + 1) k.castSucc) ω)
          (X (unitDyadicGrid (n + 1) k.succ) ω) ≤ ε)
    (i : Fin (2 ^ (n + 1) + 1)) :
    edist (X (unitDyadicGrid (n + 1) i) ω)
        (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) ≤ ε := by sorry
