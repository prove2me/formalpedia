-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_eq_smul_of_commute
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_eq_smul_of_commute
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:22.448951+00:00
-- url     : https://prove2.me/theorems/1ccb8cbe-4e52-4f0e-a4d5-b6110928813e
-- title:
--   Restricted Tensor: exists eq smul of commute
-- statement:
--   The Restricted Tensor construction uses the exists eq smul of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L178-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L178-L212

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_eq_smul_of_commute [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) [FiniteDimensional ℂ (LinearMap.range e)] {T : End ℂ V}
    (hTρ : ∀ m, T * ρ m = ρ m * T) (hTe : T * e = e * T) : ∃ c : ℂ, T = c • 1 := by sorry
