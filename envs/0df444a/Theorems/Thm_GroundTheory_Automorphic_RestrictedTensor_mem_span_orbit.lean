-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_orbit
-- name    : GroundTheory.Automorphic.RestrictedTensor.mem_span_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:31.241339+00:00
-- url     : https://prove2.me/theorems/ec2a9bea-c33d-4500-8691-f177b21b005b
-- title:
--   Restricted Tensor: mem span orbit
-- statement:
--   The Restricted Tensor construction uses the mem span orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L38-L43

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

theorem GroundTheory.Automorphic.RestrictedTensor.mem_span_orbit {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by sorry
