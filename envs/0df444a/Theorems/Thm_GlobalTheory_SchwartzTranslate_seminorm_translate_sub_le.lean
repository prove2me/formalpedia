-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslate_seminorm_translate_sub_le
-- name    : GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:37.159629+00:00
-- url     : https://prove2.me/theorems/cf82f20a-6df6-498a-a460-86d10e5893c3
-- title:
--   Schwartz Translate: seminorm translate sub le
-- statement:
--   The Schwartz Translate construction uses the seminorm translate sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L89-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L89-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzTranslate

theorem GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (f : 𝓢(V, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by sorry
