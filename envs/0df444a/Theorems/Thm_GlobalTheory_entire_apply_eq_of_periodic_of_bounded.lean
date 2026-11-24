-- Prove2me | Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_bounded
-- name    : GlobalTheory.entire_apply_eq_of_periodic_of_bounded
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:29.573008+00:00
-- url     : https://prove2.me/theorems/0466d0bb-d894-4728-b9b6-79218a8e0371
-- title:
--   Global Theory: entire apply eq of periodic of bounded
-- statement:
--   The Global Theory construction uses the entire apply eq of periodic of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L27-L34

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

theorem GlobalTheory.entire_apply_eq_of_periodic_of_bounded [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) {G K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by sorry
