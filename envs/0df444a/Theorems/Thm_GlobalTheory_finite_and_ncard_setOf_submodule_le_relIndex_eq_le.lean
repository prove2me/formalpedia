-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_ncard_setOf_submodule_le_relIndex_eq_le
-- name    : GlobalTheory.finite_and_ncard_setOf_submodule_le_relIndex_eq_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:48.845968+00:00
-- url     : https://prove2.me/theorems/f7e9ff65-9c15-50fb-9780-704e0d9853be
-- title:
--   Global Theory: finite and ncard set Of submodule le rel Index eq le
-- statement:
--   The Global Theory construction uses the finite and ncard set Of submodule le rel Index eq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L147-L156

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

theorem GlobalTheory.finite_and_ncard_setOf_submodule_le_relIndex_eq_le {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤
      m ^ finrank ℤ L := by sorry
