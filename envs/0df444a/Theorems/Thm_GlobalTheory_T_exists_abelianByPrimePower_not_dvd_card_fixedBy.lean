-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_abelianByPrimePower_not_dvd_card_fixedBy
-- name    : GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:18.230853+00:00
-- url     : https://prove2.me/theorems/0ec37582-3983-4217-bf4c-87dc592c4915
-- title:
--   T: exists abelian By Prime Power not dvd card fixed By
-- statement:
--   The T construction uses the exists abelian By Prime Power not dvd card fixed By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsAbelianByPrimePowerNotDvdCardFixedByStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsAbelianByPrimePowerNotDvdCardFixedByStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedBy
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedByStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by sorry
