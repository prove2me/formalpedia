-- Prove2me | Theorems.Thm_GlobalTheory_IntegralNormAtMostOne_norm_le_one_of_isIntegral
-- name    : GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:55.125405+00:00
-- url     : https://prove2.me/theorems/07bd8ba6-14fa-4984-bae9-52a8f24e826b
-- title:
--   Integral Norm At Most One: norm le one of is Integral
-- statement:
--   The Integral Norm At Most One construction uses the norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherTail.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherTail.lean#L5-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralNormAtMostOne

theorem GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by sorry
