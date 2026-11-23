-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_single
-- name    : GroundTheory.Automorphic.RestrictedTensor.orbitMap_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:21.37693+00:00
-- url     : https://prove2.me/theorems/e6d4cd15-ec1e-4fe8-b0f6-829bc939f6a1
-- title:
--   Restricted Tensor: orbit Map single
-- statement:
--   The Restricted Tensor construction uses the orbit Map single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L69-L71

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

theorem GroundTheory.Automorphic.RestrictedTensor.orbitMap_single (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by sorry
