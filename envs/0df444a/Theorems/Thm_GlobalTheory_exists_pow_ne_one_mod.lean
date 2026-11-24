-- Prove2me | Theorems.Thm_GlobalTheory_exists_pow_ne_one_mod
-- name    : GlobalTheory.exists_pow_ne_one_mod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:23.979808+00:00
-- url     : https://prove2.me/theorems/1edd5e69-6806-4e00-9b2d-3f548f01de8d
-- title:
--   Global Theory: exists pow ne one mod
-- statement:
--   The Global Theory construction uses the exists pow ne one mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CmValuesMinPadicValBound.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CmValuesMinPadicValBound.lean#L7-L33

import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesMinPadicValBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Formalism.PairingDivisionLocalBalance

theorem GlobalTheory.exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by sorry
