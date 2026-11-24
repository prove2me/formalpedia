-- Prove2me | Theorems.Thm_GlobalTheory_succMin_comap_linearIsometry
-- name    : GlobalTheory.succMin_comap_linearIsometry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:01.027292+00:00
-- url     : https://prove2.me/theorems/f40ecd0b-7c99-44aa-8a23-f55901dfa689
-- title:
--   Global Theory: succ Min comap linear Isometry
-- statement:
--   The Global Theory construction uses the succ Min comap linear Isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L242-L245

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem GlobalTheory.succMin_comap_linearIsometry (f : F →ₗᵢ[ℝ] E) (h : (L : Set E) ⊆ Set.range f) (i : ℕ) :
    succMin (ZLattice.comap ℝ L f.toLinearMap) i = succMin L i := by sorry
