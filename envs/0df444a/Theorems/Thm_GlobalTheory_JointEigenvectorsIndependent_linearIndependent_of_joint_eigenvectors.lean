-- Prove2me | Theorems.Thm_GlobalTheory_JointEigenvectorsIndependent_linearIndependent_of_joint_eigenvectors
-- name    : GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:50.978431+00:00
-- url     : https://prove2.me/theorems/7be149dc-9799-47c3-a9ac-aeb6e80fc0a7
-- title:
--   Joint Eigenvectors Independent: linear Independent of joint eigenvectors
-- statement:
--   The Joint Eigenvectors Independent construction uses the linear Independent of joint eigenvectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfJointEigenvectors.lean#L5-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfJointEigenvectors.lean#L5-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfJointEigenvectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.JointEigenvectorsIndependent

theorem GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors {ι α M : Type} [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (χ : ι → α → ℂ) (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ)
    (hop : ∀ (a : α) (i : ι), (op a : M → M) (f i) = χ i a • f i)
    (hf : ∀ i : ι, f i ≠ (0 : M)) : LinearIndependent ℂ f := by sorry
