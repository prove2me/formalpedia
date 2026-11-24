-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isStable_comap
-- name    : GroundTheory.Automorphic.RestrictedTensor.isStable_comap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:33.079604+00:00
-- url     : https://prove2.me/theorems/0de552c8-3806-4d53-8bdb-5b52f7d8cfc5
-- title:
--   Restricted Tensor: is Stable comap
-- statement:
--   The Restricted Tensor construction uses the is Stable comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L121-L125

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

theorem GroundTheory.Automorphic.RestrictedTensor.isStable_comap (X : Subrepresentation ρ) :
    IsStable (heckeOps hρ hKc hKo) (X.toSubmodule.comap (fixedVectors ρ K).subtype) := by sorry
