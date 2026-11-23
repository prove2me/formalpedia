-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsWinProj_apply_of_mem
-- name    : GroundTheory.Automorphic.RestrictedTensor.IsWinProj.apply_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:45.302479+00:00
-- url     : https://prove2.me/theorems/58de9fd6-972c-42db-aac2-058538809bba
-- title:
--   Is Win Proj: apply of mem
-- statement:
--   The Is Win Proj construction uses the apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L140-L143

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
variable (ρ : Representation ℂ M V)
variable {ρ} {e : End ℂ V}

theorem GroundTheory.Automorphic.RestrictedTensor.IsWinProj.apply_of_mem (he : IsWinProj ρ e) {v : V} (hv : v ∈ LinearMap.range e) :
    e v = v := by sorry
