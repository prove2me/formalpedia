-- Prove2me | Theorems.Thm_GlobalTheory_succMinRadii_upper
-- name    : GlobalTheory.succMinRadii_upper
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:13.880162+00:00
-- url     : https://prove2.me/theorems/a97f62b7-4b5c-4bd4-9a8a-9759ef0737ba
-- title:
--   Global Theory: succ Min Radii upper
-- statement:
--   The Global Theory construction uses the succ Min Radii upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L46-L50

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

theorem GlobalTheory.succMinRadii_upper {r' : ℝ} (h : r ∈ succMinRadii K N S i) (hr : r ≤ r') :
    r' ∈ succMinRadii K N S i := by sorry
