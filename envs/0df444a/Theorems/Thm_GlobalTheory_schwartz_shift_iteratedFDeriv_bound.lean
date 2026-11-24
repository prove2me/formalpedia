-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_shift_iteratedFDeriv_bound
-- name    : GlobalTheory.schwartz_shift_iteratedFDeriv_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:47.721833+00:00
-- url     : https://prove2.me/theorems/133ea9d8-5f9d-4dd7-9889-4bce6b527a42
-- title:
--   Global Theory: schwartz shift iterated FDeriv bound
-- statement:
--   The Global Theory construction uses the schwartz shift iterated FDeriv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzShiftIteratedFDerivBound.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzShiftIteratedFDerivBound.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzShiftIteratedFDerivBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.schwartz_shift_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by sorry
