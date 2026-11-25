-- Prove2me | Theorems.Thm_GlobalTheory_succMinOf_pos
-- name    : GlobalTheory.succMinOf_pos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:12.567822+00:00
-- url     : https://prove2.me/theorems/89b6b14a-4d19-4831-88a6-c7aaab320826
-- title:
--   Global Theory: succ Min Of pos
-- statement:
--   The Global Theory construction uses the succ Min Of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean#L140-L144

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

theorem GlobalTheory.succMinOf_pos (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, x ≠ 0 → 0 < N x) (h1 : 1 ≤ i)
    (hi : (i : Cardinal) ≤ Module.rank K (span K S)) : 0 < succMinOf K N S i := by sorry
