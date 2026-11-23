-- Prove2me | Theorems.Thm_GlobalTheory_succMin_mono_of_isZLattice
-- name    : GlobalTheory.succMin_mono_of_isZLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:30.800866+00:00
-- url     : https://prove2.me/theorems/44cbc2d0-991a-4445-b7f8-b68c299690b4
-- title:
--   Global Theory: succ Min mono of is ZLattice
-- statement:
--   The Global Theory construction uses the succ Min mono of is ZLattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L217-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}

theorem GlobalTheory.succMin_mono_of_isZLattice [DiscreteTopology L] [IsZLattice ℝ L] (hij : i ≤ j)
    (hj : j ≤ finrank ℝ E) : succMin L i ≤ succMin L j := by sorry
