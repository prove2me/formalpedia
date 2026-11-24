-- Prove2me | Theorems.Thm_GlobalTheory_TransDecay_seminorm_mul_shift_le
-- name    : GlobalTheory.TransDecay.seminorm_mul_shift_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:12:11.259626+00:00
-- url     : https://prove2.me/theorems/4f34ceab-ae55-432b-972c-34df1200fcca
-- title:
--   Trans Decay: seminorm mul shift le
-- statement:
--   The Trans Decay construction uses the seminorm mul shift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationIsometrySchwartzOperator.lean#L7-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationIsometrySchwartzOperator.lean#L7-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationIsometrySchwartzOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
open GlobalTheory GlobalTheory.TransDecay

theorem GlobalTheory.TransDecay.seminorm_mul_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by sorry
