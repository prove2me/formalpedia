-- Prove2me | Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real
-- name    : GlobalTheory.entire_apply_eq_of_periodic_of_span_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:29.717571+00:00
-- url     : https://prove2.me/theorems/683f41ef-0ff9-4def-a942-f3666db74490
-- title:
--   Global Theory: entire apply eq of periodic of span real
-- statement:
--   The Global Theory construction uses the entire apply eq of periodic of span real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L66-L75

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

theorem GlobalTheory.entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by sorry
