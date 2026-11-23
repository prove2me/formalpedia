-- Prove2me | Theorems.Thm_GlobalTheory_finite_setOf_index_eq
-- name    : GlobalTheory.finite_setOf_index_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:21.424161+00:00
-- url     : https://prove2.me/theorems/b9a457e0-8ddd-4c10-b83a-d1f87cec5ab4
-- title:
--   Global Theory: finite set Of index eq
-- statement:
--   The Global Theory construction uses the finite set Of index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L113-L115

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

theorem GlobalTheory.finite_setOf_index_eq [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.Finite := by sorry
