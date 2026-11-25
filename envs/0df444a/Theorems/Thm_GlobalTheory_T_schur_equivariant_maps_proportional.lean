-- Prove2me | Theorems.Thm_GlobalTheory_T_schur_equivariant_maps_proportional
-- name    : GlobalTheory.T.schur_equivariant_maps_proportional
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:09.135911+00:00
-- url     : https://prove2.me/theorems/4e6af9cc-42e2-4f72-81e7-180bf4ecabc7
-- title:
--   T: schur equivariant maps proportional
-- statement:
--   The T construction uses the schur equivariant maps proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SchurEquivariantMapsProportionalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SchurEquivariantMapsProportionalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SchurEquivariantMapsProportional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SchurEquivariantMapsProportionalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schur_equivariant_maps_proportional : ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ := by sorry
