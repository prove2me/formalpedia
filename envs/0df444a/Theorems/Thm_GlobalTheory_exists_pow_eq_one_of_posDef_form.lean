-- Prove2me | Theorems.Thm_GlobalTheory_exists_pow_eq_one_of_posDef_form
-- name    : GlobalTheory.exists_pow_eq_one_of_posDef_form
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:34.563031+00:00
-- url     : https://prove2.me/theorems/d2b6b9d2-2bbb-4dd9-b399-cd3356d4af29
-- title:
--   Global Theory: exists pow eq one of pos Def form
-- statement:
--   The Global Theory construction uses the exists pow eq one of pos Def form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsPowEqOneOfPosDefForm.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsPowEqOneOfPosDefForm.lean#L6-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsPowEqOneOfPosDefForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_pow_eq_one_of_posDef_form (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (b : LinearMap.BilinForm ℤ Y) (hs : ∀ y z, b y z = b z y) (hp : ∀ y, y ≠ 0 → 0 < b y y)
    (σ : Y ≃ₗ[ℤ] Y) (hσ : ∀ y z, b (σ y) (σ z) = b y z) : ∃ n : ℕ, 0 < n ∧ σ ^ n = 1 := by sorry
