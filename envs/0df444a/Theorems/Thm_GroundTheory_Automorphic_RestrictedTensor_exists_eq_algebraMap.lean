-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_eq_algebraMap
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_eq_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:05.742719+00:00
-- url     : https://prove2.me/theorems/653bb149-2d8a-562c-844c-48aa0863b957
-- title:
--   Restricted Tensor: exists eq algebra Map
-- statement:
--   The Restricted Tensor construction uses the exists eq algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L94-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L94-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
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
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]

theorem GroundTheory.Automorphic.RestrictedTensor.exists_eq_algebraMap {T : Set (End ℂ M)} (h : IsSimpleUnder T) {φ : End ℂ M}
    (hφ : ∀ t ∈ T, Commute φ t) : ∃ c : ℂ, φ = algebraMap ℂ (End ℂ M) c := by sorry
