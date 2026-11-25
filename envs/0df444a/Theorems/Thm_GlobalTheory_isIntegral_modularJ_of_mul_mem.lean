-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_mul_mem
-- name    : GlobalTheory.isIntegral_modularJ_of_mul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:37.61679+00:00
-- url     : https://prove2.me/theorems/c32a59dd-773a-4a9b-b2a4-aa7b77599d2b
-- title:
--   Global Theory: is Integral modular J of mul mem
-- statement:
--   The Global Theory construction uses the is Integral modular J of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L283-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L283-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam

theorem GlobalTheory.isIntegral_modularJ_of_mul_mem {τ : ℍ} {α : ℂ} (hα : ∀ m : ℤ, α ≠ m)
    (h : ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1}, α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by sorry
