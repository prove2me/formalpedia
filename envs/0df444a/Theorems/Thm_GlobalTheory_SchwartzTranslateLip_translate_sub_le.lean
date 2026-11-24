-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslateLip_translate_sub_le
-- name    : GlobalTheory.SchwartzTranslateLip.translate_sub_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:20.692537+00:00
-- url     : https://prove2.me/theorems/04c26ed4-da47-4378-a2e7-ea9bf1c21cad
-- title:
--   Schwartz Translate Lip: translate sub le
-- statement:
--   The Schwartz Translate Lip construction uses the translate sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslationSeminormBound.lean#L68-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslationSeminormBound.lean#L68-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic
open GlobalTheory GlobalTheory.SchwartzTranslateLip

theorem GlobalTheory.SchwartzTranslateLip.translate_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by sorry
