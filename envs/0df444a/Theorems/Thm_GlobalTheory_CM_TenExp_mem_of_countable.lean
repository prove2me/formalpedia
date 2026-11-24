-- Prove2me | Theorems.Thm_GlobalTheory_CM_TenExp_mem_of_countable
-- name    : GlobalTheory.CM.TenExp.mem_of_countable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:39.137782+00:00
-- url     : https://prove2.me/theorems/f74a3816-fb28-4195-a988-adbd1d5a7817
-- title:
--   Ten Exp: mem of countable
-- statement:
--   The Ten Exp construction uses the mem of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L9-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp

theorem GlobalTheory.CM.TenExp.mem_of_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {Λ : Set V} (hΛ : Λ.Countable)
    (W : Submodule ℂ V) {v : V} (h : ∀ z : ℂ, ∃ l ∈ Λ, z • v - l ∈ W) : v ∈ W := by sorry
