-- Prove2me | Theorems.Thm_GlobalTheory_entire_const_of_addSubgroup_periodic
-- name    : GlobalTheory.entire_const_of_addSubgroup_periodic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:32.559823+00:00
-- url     : https://prove2.me/theorems/b01ec6bf-a565-4fd4-a121-00a8656e90b4
-- title:
--   Global Theory: entire const of add Subgroup periodic
-- statement:
--   The Global Theory construction uses the entire const of add Subgroup periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L36-L43

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

theorem GlobalTheory.entire_const_of_addSubgroup_periodic [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) (G : AddSubgroup E) {K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ g ∈ G, ∃ k ∈ K, x = g + k)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) : ∃ c, ∀ z, F z = c := by sorry
