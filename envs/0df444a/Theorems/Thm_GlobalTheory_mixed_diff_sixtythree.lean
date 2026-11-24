-- Prove2me | Theorems.Thm_GlobalTheory_mixed_diff_sixtythree
-- name    : GlobalTheory.mixed_diff_sixtythree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:20.739278+00:00
-- url     : https://prove2.me/theorems/bbd10a33-49a7-482d-9858-27d7be1ad5db
-- title:
--   Global Theory: mixed diff sixtythree
-- statement:
--   The Global Theory construction uses the mixed diff sixtythree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L47-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L47-L85

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

theorem GlobalTheory.mixed_diff_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (m : ℕ) (hm : m < 53) :
    c (m + 10) - c (m + 3) = c (m + 7) - c m := by sorry
