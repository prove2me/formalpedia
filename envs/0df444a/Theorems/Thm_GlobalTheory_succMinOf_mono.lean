-- Prove2me | Theorems.Thm_GlobalTheory_succMinOf_mono
-- name    : GlobalTheory.succMinOf_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:59.402333+00:00
-- url     : https://prove2.me/theorems/eca8c12f-e7e3-4d6a-96a6-cf8b37bb9911
-- title:
--   Global Theory: succ Min Of mono
-- statement:
--   The Global Theory construction uses the succ Min Of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L89-L92

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

theorem GlobalTheory.succMinOf_mono (hij : i ≤ j) (hj : (j : Cardinal) ≤ Module.rank K (span K S)) :
    succMinOf K N S i ≤ succMinOf K N S j := by sorry
