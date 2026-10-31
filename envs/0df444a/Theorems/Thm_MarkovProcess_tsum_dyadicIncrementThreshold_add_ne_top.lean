-- Prove2me | Theorems.Thm_MarkovProcess_tsum_dyadicIncrementThreshold_add_ne_top
-- name    : MarkovProcess.tsum_dyadicIncrementThreshold_add_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:01.020449+00:00
-- url     : https://prove2.me/theorems/da65208d-c359-4ef0-abf6-ae8eebcb155b
-- title:
--   MarkovProcess: tsum_dyadicIncrementThreshold_add_ne_top
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal










end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]















end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal














end DyadicThresholdTail

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/






open scoped ENNReal NNReal










open MarkovProcess in

theorem MarkovProcess.tsum_dyadicIncrementThreshold_add_ne_top {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    (∑' k : ℕ, dyadicIncrementThreshold γ (n + k)) ≠ ∞ := by sorry
