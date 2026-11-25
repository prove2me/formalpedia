-- Prove2me | Theorems.Thm_GlobalTheory_CM_TenExp_linear_eq_of_countable
-- name    : GlobalTheory.CM.TenExp.linear_eq_of_countable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:49.392441+00:00
-- url     : https://prove2.me/theorems/817b8d08-ea79-545b-96b6-e97324bf7c5d
-- title:
--   Ten Exp: linear eq of countable
-- statement:
--   The Ten Exp construction uses the linear eq of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L24-L29

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

theorem GlobalTheory.CM.TenExp.linear_eq_of_countable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {Λ : Set V} (hΛ : Λ.Countable) {F F' : U →ₗ[ℂ] V} (h : ∀ u, F u - F' u ∈ Λ) : F = F' := by sorry
