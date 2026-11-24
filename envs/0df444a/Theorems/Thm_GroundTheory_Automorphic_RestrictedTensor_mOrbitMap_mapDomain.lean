-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mOrbitMap_mapDomain
-- name    : GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_mapDomain
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:25.962938+00:00
-- url     : https://prove2.me/theorems/bc2aa9ca-024f-4539-955e-9ff94f5a2403
-- title:
--   Restricted Tensor: m Orbit Map map Domain
-- statement:
--   The Restricted Tensor construction uses the m Orbit Map map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L63-L68

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

theorem GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_mapDomain (ρ : Representation ℂ M V) (v : V) (h : M) (c : M →₀ ℂ) :
    mOrbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (mOrbitMap ρ v c) := by sorry
