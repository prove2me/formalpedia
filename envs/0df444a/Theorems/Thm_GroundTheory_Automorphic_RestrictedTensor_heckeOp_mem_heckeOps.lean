-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_mem_heckeOps
-- name    : GroundTheory.Automorphic.RestrictedTensor.heckeOp_mem_heckeOps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:08.000811+00:00
-- url     : https://prove2.me/theorems/f54b58f4-c268-4ff3-b8ce-421ca61a5ed1
-- title:
--   Restricted Tensor: hecke Op mem hecke Ops
-- statement:
--   The Restricted Tensor construction uses the hecke Op mem hecke Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L77-L78

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

theorem GroundTheory.Automorphic.RestrictedTensor.heckeOp_mem_heckeOps (g : G) : heckeOp hρ hKc hKo g ∈ heckeOps hρ hKc hKo := by sorry
