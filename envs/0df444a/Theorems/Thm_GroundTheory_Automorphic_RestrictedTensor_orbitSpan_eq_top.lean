-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitSpan_eq_top
-- name    : GroundTheory.Automorphic.RestrictedTensor.orbitSpan_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:36.273798+00:00
-- url     : https://prove2.me/theorems/db07c7c4-3b2a-4d66-a830-8195185258f6
-- title:
--   Restricted Tensor: orbit Span eq top
-- statement:
--   The Restricted Tensor construction uses the orbit Span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L28-L36

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

theorem GroundTheory.Automorphic.RestrictedTensor.orbitSpan_eq_top {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by sorry
