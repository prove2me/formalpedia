-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:12.740152+00:00
-- url     : https://prove2.me/theorems/276091c4-ea4a-4aa6-9c06-f2ddbf6f9391
-- title:
--   Restricted Tensor: eq zero of forall apply
-- statement:
--   The Restricted Tensor construction uses the eq zero of forall apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L45-L55

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by sorry
