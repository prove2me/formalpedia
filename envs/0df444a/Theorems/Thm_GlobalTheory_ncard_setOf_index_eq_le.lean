-- Prove2me | Theorems.Thm_GlobalTheory_ncard_setOf_index_eq_le
-- name    : GlobalTheory.ncard_setOf_index_eq_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:12.193803+00:00
-- url     : https://prove2.me/theorems/f5f3b5f8-1ab8-4341-90ac-43571de42cb3
-- title:
--   Global Theory: ncard set Of index eq le
-- statement:
--   The Global Theory construction uses the ncard set Of index eq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L117-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]

theorem GlobalTheory.ncard_setOf_index_eq_le [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.ncard ≤ m ^ finrank ℤ M := by sorry
