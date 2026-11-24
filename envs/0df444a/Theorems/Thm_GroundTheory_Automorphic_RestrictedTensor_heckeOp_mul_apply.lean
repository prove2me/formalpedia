-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_mul_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.heckeOp_mul_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:29.327453+00:00
-- url     : https://prove2.me/theorems/d89ef77e-4161-4bfa-93a0-5fc5c75e23f5
-- title:
--   Restricted Tensor: hecke Op mul apply
-- statement:
--   The Restricted Tensor construction uses the hecke Op mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L88-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L88-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

theorem GroundTheory.Automorphic.RestrictedTensor.heckeOp_mul_apply {a b : G}
    (hab : ∀ h ∈ K, ∃ k ∈ K, k * a = a * k ∧ (k⁻¹ * h) * b = b * (k⁻¹ * h))
    (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo a (heckeOp hρ hKc hKo b m) = heckeOp hρ hKc hKo (a * b) m := by sorry
