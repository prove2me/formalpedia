-- Prove2me | Theorems.Thm_GlobalTheory_norm_sq_adjoint_add_ge_of_joint_eigenspaces
-- name    : GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:09.695914+00:00
-- url     : https://prove2.me/theorems/e2c9cb48-f071-5b04-85b2-76ce9b6d2426
-- title:
--   Global Theory: norm sq adjoint add ge of joint eigenspaces
-- statement:
--   The Global Theory construction uses the norm sq adjoint add ge of joint eigenspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormSqAdjointAddGeOfJointEigenspaces.lean#L7-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormSqAdjointAddGeOfJointEigenspaces.lean#L7-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSqAdjointAddGeOfJointEigenspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped InnerProductSpace

theorem GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by sorry
