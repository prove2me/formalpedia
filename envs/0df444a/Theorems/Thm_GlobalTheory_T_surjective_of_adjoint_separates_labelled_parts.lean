-- Prove2me | Theorems.Thm_GlobalTheory_T_surjective_of_adjoint_separates_labelled_parts
-- name    : GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:27.873808+00:00
-- url     : https://prove2.me/theorems/a8fe507c-51f4-4697-919e-42e8d19142f5
-- title:
--   T: surjective of adjoint separates labelled parts
-- statement:
--   The T construction uses the surjective of adjoint separates labelled parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledPartsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledPartsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledPartsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by sorry
