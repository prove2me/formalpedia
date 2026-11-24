-- Prove2me | Theorems.Thm_GlobalTheory_pos_of_pos_mul_inner_on_joint_eigenvectors
-- name    : GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:44.78599+00:00
-- url     : https://prove2.me/theorems/e286a393-4ced-4b8c-a63c-8dc255e2dffc
-- title:
--   Global Theory: pos of pos mul inner on joint eigenvectors
-- statement:
--   The Global Theory construction uses the pos of pos mul inner on joint eigenvectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosOfPosMulInnerOnJointEigenvectors.lean#L57-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosOfPosMulInnerOnJointEigenvectors.lean#L57-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosOfPosMulInnerOnJointEigenvectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module.End

theorem GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by sorry
