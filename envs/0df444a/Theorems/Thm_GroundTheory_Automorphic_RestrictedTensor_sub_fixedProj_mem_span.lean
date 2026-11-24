-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_sub_fixedProj_mem_span
-- name    : GroundTheory.Automorphic.RestrictedTensor.sub_fixedProj_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:05.855797+00:00
-- url     : https://prove2.me/theorems/a1ae1a42-602f-48b2-abcb-1bf6d37ffb6b
-- title:
--   Restricted Tensor: sub fixed Proj mem span
-- statement:
--   The Restricted Tensor construction uses the sub fixed Proj mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L19-L52

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

theorem GroundTheory.Automorphic.RestrictedTensor.sub_fixedProj_mem_span (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (u : V) :
    u - (fixedProj ρ hρ hKc hKo u : V) ∈
      Submodule.span ℂ (range fun k : K => ρ k u - u) := by sorry
