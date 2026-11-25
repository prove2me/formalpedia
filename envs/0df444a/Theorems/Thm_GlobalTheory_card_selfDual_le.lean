-- Prove2me | Theorems.Thm_GlobalTheory_card_selfDual_le
-- name    : GlobalTheory.card_selfDual_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:27.846852+00:00
-- url     : https://prove2.me/theorems/40ed8849-e74e-49df-9688-1c57d1084393
-- title:
--   Global Theory: card self Dual le
-- statement:
--   The Global Theory construction uses the card self Dual le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L137-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RelIndexDualSubmoduleInfOfSelfDual.lean#L137-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
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

theorem GlobalTheory.card_selfDual_le {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hlr : ∀ x y, B x y = B y x ∨ B x y = - B y x) (L : Submodule ℤ V) (hL : L.FG) (hLd : B.dualSubmodule L = L) (m : ℕ) (hm : 1 ≤ m) :
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤ m ^ (2 * Module.finrank ℚ V) ∧
    ∀ L' : Submodule ℤ V, L'.FG → B.dualSubmodule L' = L' → L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧ (L'.toAddSubgroup.relIndex L.toAddSubgroup = 1 → L' = L) := by sorry
