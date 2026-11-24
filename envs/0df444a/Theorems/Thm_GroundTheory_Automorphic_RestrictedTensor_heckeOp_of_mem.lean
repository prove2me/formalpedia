-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_of_mem
-- name    : GroundTheory.Automorphic.RestrictedTensor.heckeOp_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:19.062717+00:00
-- url     : https://prove2.me/theorems/bb33ea82-907a-4dde-8632-12d814e44380
-- title:
--   Restricted Tensor: hecke Op of mem
-- statement:
--   The Restricted Tensor construction uses the hecke Op of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L80-L83

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

theorem GroundTheory.Automorphic.RestrictedTensor.heckeOp_of_mem {g : G} (hg : g ∈ K) : heckeOp hρ hKc hKo g = 1 := by sorry
