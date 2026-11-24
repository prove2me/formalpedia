-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslateUnif_seminorm_translate_sub_lineDeriv_le
-- name    : GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:56.968421+00:00
-- url     : https://prove2.me/theorems/4b778054-a2e3-45f2-bafb-34b4fd9ca7ba
-- title:
--   Schwartz Translate Unif: seminorm translate sub line Deriv le
-- statement:
--   The Schwartz Translate Unif construction uses the seminorm translate sub line Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrder.lean#L102-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrder.lean#L102-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
open GlobalTheory GlobalTheory.SchwartzTranslateUnif
open GlobalTheory.SchwartzTranslate

theorem GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : 𝓢(X, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f
        - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by sorry
