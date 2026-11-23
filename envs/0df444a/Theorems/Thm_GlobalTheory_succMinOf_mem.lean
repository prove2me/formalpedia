-- Prove2me | Theorems.Thm_GlobalTheory_succMinOf_mem
-- name    : GlobalTheory.succMinOf_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:20.089682+00:00
-- url     : https://prove2.me/theorems/283492ae-b661-4056-951d-3f3cfab6e7e0
-- title:
--   Global Theory: succ Min Of mem
-- statement:
--   The Global Theory construction uses the succ Min Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L122-L138

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
variable (K : Type*) [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {K}
variable {N N' : V → ℝ} {S S' : Set V} {i j : ℕ} {r : ℝ}

theorem GlobalTheory.succMinOf_mem (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hi : (i : Cardinal) ≤ Module.rank K (span K S)) :
    succMinOf K N S i ∈ succMinRadii K N S i := by sorry
