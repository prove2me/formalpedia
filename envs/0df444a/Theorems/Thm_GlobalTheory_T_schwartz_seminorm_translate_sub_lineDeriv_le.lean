-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_seminorm_translate_sub_lineDeriv_le
-- name    : GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:52.45587+00:00
-- url     : https://prove2.me/theorems/99cb9d02-39dc-57a6-9a79-b5304ee99c5e
-- title:
--   T: schwartz seminorm translate sub line Deriv le
-- statement:
--   The T construction uses the schwartz seminorm translate sub line Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by sorry
