-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_sub_le_of_bound
-- name    : GlobalTheory.norm_iteratedFDeriv_sub_le_of_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:02.419782+00:00
-- url     : https://prove2.me/theorems/790326d4-5098-412d-a210-9d9e7a75aa0d
-- title:
--   Global Theory: norm iterated FDeriv sub le of bound
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv sub le of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L58-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.norm_iteratedFDeriv_sub_le_of_bound {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : V → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hC : ∀ v, ‖iteratedFDeriv ℝ (n + 1) f v‖ ≤ C) (a b : V) :
    ‖iteratedFDeriv ℝ n f a - iteratedFDeriv ℝ n f b‖ ≤ C * ‖a - b‖ := by sorry
