-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_mapDomain
-- name    : GroundTheory.Automorphic.RestrictedTensor.orbitMap_mapDomain
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:47.306063+00:00
-- url     : https://prove2.me/theorems/22af8d55-228d-403d-9dfb-9101d9377aba
-- title:
--   Restricted Tensor: orbit Map map Domain
-- statement:
--   The Restricted Tensor construction uses the orbit Map map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L73-L78

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

theorem GroundTheory.Automorphic.RestrictedTensor.orbitMap_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by sorry
