-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_range_orbitMap
-- name    : GroundTheory.Automorphic.RestrictedTensor.range_orbitMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:42.9663+00:00
-- url     : https://prove2.me/theorems/0ec320ee-5f17-4472-968c-ae96fde95884
-- title:
--   Restricted Tensor: range orbit Map
-- statement:
--   The Restricted Tensor construction uses the range orbit Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L80-L82

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

theorem GroundTheory.Automorphic.RestrictedTensor.range_orbitMap (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by sorry
