-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSimpleUnder_heckeOps
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_heckeOps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:33.247403+00:00
-- url     : https://prove2.me/theorems/c38d4392-843d-4b6d-9268-9b129a449cbe
-- title:
--   Restricted Tensor: is Simple Under hecke Ops
-- statement:
--   The Restricted Tensor construction uses the is Simple Under hecke Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L127-L146

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

theorem GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_heckeOps [ρ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleUnder (heckeOps hρ hKc hKo) := by sorry
