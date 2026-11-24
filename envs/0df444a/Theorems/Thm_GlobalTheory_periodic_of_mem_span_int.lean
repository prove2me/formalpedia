-- Prove2me | Theorems.Thm_GlobalTheory_periodic_of_mem_span_int
-- name    : GlobalTheory.periodic_of_mem_span_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:48.797227+00:00
-- url     : https://prove2.me/theorems/1ceabb6e-1f3a-476a-b449-614866fae1e1
-- title:
--   Global Theory: periodic of mem span int
-- statement:
--   The Global Theory construction uses the periodic of mem span int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L53-L64

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
omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by sorry
