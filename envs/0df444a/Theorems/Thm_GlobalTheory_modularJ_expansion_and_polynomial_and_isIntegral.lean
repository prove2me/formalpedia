-- Prove2me | Theorems.Thm_GlobalTheory_modularJ_expansion_and_polynomial_and_isIntegral
-- name    : GlobalTheory.modularJ_expansion_and_polynomial_and_isIntegral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:01.622851+00:00
-- url     : https://prove2.me/theorems/04b27153-84aa-5556-8347-45833d0282cb
-- title:
--   Global Theory: modular J expansion and polynomial and is Integral
-- statement:
--   The Global Theory construction uses the modular J expansion and polynomial and is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L348-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L348-L364

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

theorem GlobalTheory.modularJ_expansion_and_polynomial_and_isIntegral :
    (∃ c : ℕ → ℤ, ∀ τ : ℍ,
      HasSum (fun n ↦ (c n : ℂ) * 𝕢 1 τ ^ n) (modularJ τ - (𝕢 1 τ)⁻¹)) ∧
    (∀ (m : ℕ) (f : ℍ → ℂ), (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) → MDiff f →
      (IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        (∀ i, P.coeff i ∈ AddSubgroup.closure
          (Set.range fun k ↦ coeff k (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ))) ∧
        ∀ τ, f τ = P.eval (modularJ τ)) ∧
    (∀ (w : ℍ) (d : ℤ), (2 * (w : ℂ) - 1) ^ 2 = -d → IsIntegral ℤ (modularJ w)) ∧
    (∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (τ : ℍ),
      (∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
        ι α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) → IsIntegral ℤ (modularJ τ)) := by sorry
