-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mOrbitMap_single
-- name    : GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:59.382891+00:00
-- url     : https://prove2.me/theorems/1f1d4eea-23cd-40e9-8449-21d7bd99f05d
-- title:
--   Restricted Tensor: m Orbit Map single
-- statement:
--   The Restricted Tensor construction uses the m Orbit Map single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L59-L61

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
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
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_single (ρ : Representation ℂ M V) (v : V) (m : M) (a : ℂ) :
    mOrbitMap ρ v (Finsupp.single m a) = a • ρ m v := by sorry
