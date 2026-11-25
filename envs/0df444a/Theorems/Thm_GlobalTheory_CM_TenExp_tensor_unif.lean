-- Prove2me | Theorems.Thm_GlobalTheory_CM_TenExp_tensor_unif
-- name    : GlobalTheory.CM.TenExp.tensor_unif
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:53.580869+00:00
-- url     : https://prove2.me/theorems/330e06a0-6d8e-4440-9df7-7be09c59120e
-- title:
--   Ten Exp: tensor unif
-- statement:
--   The Ten Exp construction uses the tensor unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L43-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L43-L89

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

theorem GlobalTheory.CM.TenExp.tensor_unif {X Y V : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [AddCommGroup V] [Module ℂ V] (eqv : M ⊗[O] X ≃ₗ[O] Y) (e₀ : ℂ →ₗ[O] X)
    (hs : Function.Surjective e₀) (hk : ∀ z, e₀ z = 0 ↔ z ∈ Set.range (algebraMap O ℂ)) (ex : V →+ Y)
    (hΛ : Set.Countable {v | ex v = 0}) (P : M →+ V) (hP : ∀ (o : O) a, P (o • a) = algebraMap O ℂ o • P a)
    (hi : Function.Injective P) (hex : ∀ (z : ℂ) a, ex (z • P a) = eqv (a ⊗ₜ e₀ z)) :
    Submodule.span ℂ (Set.range P) = ⊤ ∧ (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
      ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (f : M →+ V'), (∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) →
        ∃ F : V →ₗ[ℂ] V', ∀ a, F (P a) = f a := by sorry
