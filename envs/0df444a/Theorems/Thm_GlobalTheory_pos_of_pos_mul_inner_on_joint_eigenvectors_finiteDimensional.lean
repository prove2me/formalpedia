-- Prove2me | Theorems.Thm_GlobalTheory_pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional
-- name    : GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:44.40287+00:00
-- url     : https://prove2.me/theorems/d55c9ab8-56a2-4085-b26a-eb4c21d6fce1
-- title:
--   Global Theory: pos of pos mul inner on joint eigenvectors finite Dimensional
-- statement:
--   The Global Theory construction uses the pos of pos mul inner on joint eigenvectors finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosOfPosMulInnerOnJointEigenvectors.lean#L7-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosOfPosMulInnerOnJointEigenvectors.lean#L7-L55

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

theorem GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional {E H I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsSymmetric) (hc : ∀ i j, Commute (T i) (T j))
    (j u : E →ₗ[ℂ] H)
    (hu : ∀ (m : I → ℝ) (y : E), (∀ i, T i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, inner ℂ (j x) (u y) = (c : ℂ) * inner ℂ x y)
    (x : E) (hx : x ≠ 0) : (inner ℂ (j x) (u x)).im = 0 ∧ 0 < (inner ℂ (j x) (u x)).re := by sorry
