-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_orbitSpan_self
-- name    : GroundTheory.Automorphic.RestrictedTensor.mem_orbitSpan_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:01.068021+00:00
-- url     : https://prove2.me/theorems/470fbb47-c2f3-4fb7-897f-2987a06b8717
-- title:
--   Restricted Tensor: mem orbit Span self
-- statement:
--   The Restricted Tensor construction uses the mem orbit Span self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L25-L26

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

theorem GroundTheory.Automorphic.RestrictedTensor.mem_orbitSpan_self (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule := by sorry
