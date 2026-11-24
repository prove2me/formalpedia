-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_const_mul
-- name    : GlobalTheory.QFam.HasQ.const_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:24.522597+00:00
-- url     : https://prove2.me/theorems/e6044070-3c2a-4820-b43b-8ea3027c6165
-- title:
--   Has Q: const mul
-- statement:
--   The Has Q construction uses the const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.HasQ.const_mul {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by sorry
