-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_place_not_isSquare_adicCompletion
-- name    : GlobalTheory.T.exists_place_not_isSquare_adicCompletion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:55.510929+00:00
-- url     : https://prove2.me/theorems/6704d966-edcd-431a-9387-e3463ba100ee
-- title:
--   T: exists place not is Square adic Completion
-- statement:
--   The T construction uses the exists place not is Square adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPlaceNotIsSquareAdicCompletionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPlaceNotIsSquareAdicCompletionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceNotIsSquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceNotIsSquareAdicCompletionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_place_not_isSquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by sorry
