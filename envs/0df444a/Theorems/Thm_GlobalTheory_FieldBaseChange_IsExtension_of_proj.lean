-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_of_proj
-- name    : GlobalTheory.FieldBaseChange.IsExtension.of_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:25.579424+00:00
-- url     : https://prove2.me/theorems/3c782b8f-6189-4d5d-9818-865002fccf85
-- title:
--   Is Extension: of proj
-- statement:
--   The Is Extension construction uses the of proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L103-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L103-L143

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

theorem GlobalTheory.FieldBaseChange.IsExtension.of_proj {J : Type} {P Q : J → Type} [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module F (Q j)] (a : V →ₛₗ[algebraMap K F] W)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] Q j) (hb : ∀ j, IsExtension (b j))
    (π : ∀ j, V →ₗ[K] P j) (π' : ∀ j, W →ₗ[F] Q j) (comm : ∀ j v, π' j (a v) = b j (π j v))
    (inj' : ∀ x, (∀ j, π' j x = 0) → x = 0) (T : Finset J) (inj : ∀ v, (∀ j ∈ T, π j v = 0) → v = 0)
    (desc : ∀ (ℓ : F →ₗ[K] K) (Λ : ∀ j, Q j →+ P j), (∀ j, IsCoord (b j) ℓ (Λ j)) →
      ∀ x, ∃ v, ∀ j, π j v = Λ j (π' j x)) : IsExtension a := by sorry
