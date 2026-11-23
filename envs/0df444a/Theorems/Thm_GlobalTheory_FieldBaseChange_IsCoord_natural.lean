-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_IsCoord_natural
-- name    : GlobalTheory.FieldBaseChange.IsCoord.natural
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:00.515913+00:00
-- url     : https://prove2.me/theorems/8294d8c0-31c7-4db2-8aa4-b80198033e5f
-- title:
--   Is Coord: natural
-- statement:
--   The Is Coord construction uses the natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L41-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

theorem GlobalTheory.FieldBaseChange.IsCoord.natural {V' W' : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module F W']
    {a : V →ₛₗ[algebraMap K F] W} {a' : V' →ₛₗ[algebraMap K F] W'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : W →+ V} {Λ' : W' →+ V'}
    (hΛ : IsCoord a ℓ Λ) (hΛ' : IsCoord a' ℓ Λ') (θ : V →ₗ[K] V') (θ' : W →ₗ[F] W')
    (hθ : ∀ v, θ' (a v) = a' (θ v)) (x : W) : Λ' (θ' x) = θ (Λ x) := by sorry
