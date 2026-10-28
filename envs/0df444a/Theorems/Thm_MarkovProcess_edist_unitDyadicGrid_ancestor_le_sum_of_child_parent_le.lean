-- Prove2me | Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
-- name    : MarkovProcess.edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:49:15.82787+00:00
-- url     : https://prove2.me/theorems/7dc7b95d-1f0f-45b7-abed-a3be870cede8
-- title:
--   Dyadic ancestor increments bounded by child-parent sums
-- statement:
--   Iterating child-to-parent bounds controls the increment from a fine-grid point to its
--   canonical ancestor by the corresponding finite sum.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicChaining.lean#L217-L262

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
open MarkovProcess MarkovProcess
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























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem MarkovProcess.edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
    {X : NNRat → Ω → E} {n r : ℕ} {δ : ℕ → ℝ≥0∞} {ω : Ω}
    (hparent : ∀ s < r, ∀ i : Fin (2 ^ (n + s + 1) + 1),
      edist (X (unitDyadicGrid (n + s + 1) i) ω)
          (X (unitDyadicGrid (n + s) (unitDyadicParentIndex (n + s) i)) ω) ≤
        δ (n + s + 1))
    (i : Fin (2 ^ (n + r) + 1)) :
    edist (X (unitDyadicGrid (n + r) i) ω)
        (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
      ∑ s ∈ Finset.range r, δ (n + s + 1) := by sorry
