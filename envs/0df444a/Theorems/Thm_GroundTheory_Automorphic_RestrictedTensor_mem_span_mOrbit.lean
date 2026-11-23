-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_mOrbit
-- name    : GroundTheory.Automorphic.RestrictedTensor.mem_span_mOrbit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:21.845137+00:00
-- url     : https://prove2.me/theorems/e3183ce1-b564-4269-9f9d-e1b01fc37079
-- title:
--   Restricted Tensor: mem span m Orbit
-- statement:
--   The Restricted Tensor construction uses the mem span m Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L32-L42

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

theorem GroundTheory.Automorphic.RestrictedTensor.mem_span_mOrbit {ρ : Representation ℂ M V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    (x : V) : x ∈ Submodule.span ℂ (range fun m => ρ m v) := by sorry
