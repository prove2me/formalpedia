-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_natCast_mem_differentIdeal_pow_le_discr_sq
-- name    : GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:48.485849+00:00
-- url     : https://prove2.me/theorems/ae7f774d-a23f-45e5-aadb-121fdc655d50
-- title:
--   T: exists nat Cast mem different Ideal pow le discr sq
-- statement:
--   The T construction uses the exists nat Cast mem different Ideal pow le discr sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatCastMemDifferentIdealPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatCastMemDifferentIdealPowLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧ ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧ (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by sorry
