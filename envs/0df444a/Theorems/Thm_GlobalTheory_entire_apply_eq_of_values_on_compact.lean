-- Prove2me | Theorems.Thm_GlobalTheory_entire_apply_eq_of_values_on_compact
-- name    : GlobalTheory.entire_apply_eq_of_values_on_compact
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:46.731788+00:00
-- url     : https://prove2.me/theorems/ef66d102-1688-41a5-a641-35001d77ff6c
-- title:
--   Global Theory: entire apply eq of values on compact
-- statement:
--   The Global Theory construction uses the entire apply eq of values on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.entire_apply_eq_of_values_on_compact {F : E → V} (hF : Differentiable ℂ F) {K : Set E}
    (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, F x = F k) (z w : E) : F z = F w := by sorry
