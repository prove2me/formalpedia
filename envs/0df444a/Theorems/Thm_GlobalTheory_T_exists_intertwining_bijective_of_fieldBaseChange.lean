-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_intertwining_bijective_of_fieldBaseChange
-- name    : GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:11.555149+00:00
-- url     : https://prove2.me/theorems/ac5e0a5e-4f5e-40fd-83d7-e9e67d6b9cc6
-- title:
--   T: exists intertwining bijective of field Base Change
-- statement:
--   The T construction uses the exists intertwining bijective of field Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntertwiningBijectiveOfFieldBaseChangeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntertwiningBijectiveOfFieldBaseChangeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by sorry
