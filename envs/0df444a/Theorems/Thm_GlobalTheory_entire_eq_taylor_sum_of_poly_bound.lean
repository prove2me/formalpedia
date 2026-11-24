-- Prove2me | Theorems.Thm_GlobalTheory_entire_eq_taylor_sum_of_poly_bound
-- name    : GlobalTheory.entire_eq_taylor_sum_of_poly_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:43.352141+00:00
-- url     : https://prove2.me/theorems/9f866930-b04a-4f5f-b9b3-1e26d9c0726d
-- title:
--   Global Theory: entire eq taylor sum of poly bound
-- statement:
--   The Global Theory construction uses the entire eq taylor sum of poly bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L108-L119

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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by sorry
