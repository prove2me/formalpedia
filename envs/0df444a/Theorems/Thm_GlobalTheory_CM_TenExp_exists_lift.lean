-- Prove2me | Theorems.Thm_GlobalTheory_CM_TenExp_exists_lift
-- name    : GlobalTheory.CM.TenExp.exists_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:03:09.893602+00:00
-- url     : https://prove2.me/theorems/898f8ffb-8fc7-4b30-a817-b9a03fb1c784
-- title:
--   Ten Exp: exists lift
-- statement:
--   The Ten Exp construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L35-L41

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
variable {O M : Type} [CommRing O] [Algebra O ℂ] [AddCommGroup M] [Module O M]

theorem GlobalTheory.CM.TenExp.exists_lift {V : Type} [AddCommGroup V] [Module ℂ V] (f : M →+ V)
    (hf : ∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) :
    ∃ F : ℂ ⊗[O] M →ₗ[ℂ] V, ∀ z a, F (z ⊗ₜ a) = z • f a := by sorry
