-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_ringOfIntegers
-- name    : GlobalTheory.isIntegral_modularJ_of_ringOfIntegers
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:44.342622+00:00
-- url     : https://prove2.me/theorems/bc228839-ddbc-4715-a2df-da32c3179eb1
-- title:
--   Global Theory: is Integral modular J of ring Of Integers
-- statement:
--   The Global Theory construction uses the is Integral modular J of ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L297-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L297-L312

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
open NumberField

theorem GlobalTheory.isIntegral_modularJ_of_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (ι : K →+* ℂ) {τ : ℍ}
    (h : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
      ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by sorry
