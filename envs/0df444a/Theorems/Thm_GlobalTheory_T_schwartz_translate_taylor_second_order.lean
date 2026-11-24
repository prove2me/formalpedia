-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_translate_taylor_second_order
-- name    : GlobalTheory.T.schwartz_translate_taylor_second_order
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:13.231313+00:00
-- url     : https://prove2.me/theorems/c9f2661d-b6e5-4d40-b3f7-198d090a6a72
-- title:
--   T: schwartz translate taylor second order
-- statement:
--   The T construction uses the schwartz translate taylor second order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrderStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrderStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrderStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by sorry
