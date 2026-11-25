-- Prove2me | Theorems.Thm_GlobalTheory_T_hasQExpansionOfLevel_coeff_and_function_unique
-- name    : GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:06.890475+00:00
-- url     : https://prove2.me/theorems/07810773-9a2d-412a-9bb3-9c5a4e4b2f7a
-- title:
--   T: has QExpansion Of Level coeff and function unique
-- statement:
--   The T construction uses the has QExpansion Of Level coeff and function unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUniqueStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUniqueStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique : (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧ (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by sorry
