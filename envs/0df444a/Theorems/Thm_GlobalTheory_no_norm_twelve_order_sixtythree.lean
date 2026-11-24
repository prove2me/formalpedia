-- Prove2me | Theorems.Thm_GlobalTheory_no_norm_twelve_order_sixtythree
-- name    : GlobalTheory.no_norm_twelve_order_sixtythree
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:32.303998+00:00
-- url     : https://prove2.me/theorems/2ee377b2-a325-4f44-ba0b-1bcf0005ed71
-- title:
--   Global Theory: no norm twelve order sixtythree
-- statement:
--   The Global Theory construction uses the no norm twelve order sixtythree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L107-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L107-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.no_norm_twelve_order_sixtythree : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 →
    ∑ k ∈ Finset.range 63, c k ^ 2 = 12 →
    (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by sorry
