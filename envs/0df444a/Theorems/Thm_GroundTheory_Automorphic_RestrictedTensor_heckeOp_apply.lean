-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.heckeOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:24.614262+00:00
-- url     : https://prove2.me/theorems/868482a1-dcaa-4142-a552-73cc9d2af934
-- title:
--   Restricted Tensor: hecke Op apply
-- statement:
--   The Restricted Tensor construction uses the hecke Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L73-L75

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

theorem GroundTheory.Automorphic.RestrictedTensor.heckeOp_apply (g : G) (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo g m = fixedProj ρ hρ hKc hKo (ρ g m) := by sorry
