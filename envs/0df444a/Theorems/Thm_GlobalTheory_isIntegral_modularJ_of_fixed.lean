-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_fixed
-- name    : GlobalTheory.isIntegral_modularJ_of_fixed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:08.486799+00:00
-- url     : https://prove2.me/theorems/0eb262d5-e3ce-48d4-8fab-0536d715db38
-- title:
--   Global Theory: is Integral modular J of fixed
-- statement:
--   The Global Theory construction uses the is Integral modular J of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L195-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L195-L247

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

theorem GlobalTheory.isIntegral_modularJ_of_fixed {n : ℕ} (hsq : ¬ IsSquare n)
    (M : FixedDetMatrix (Fin 2) ℤ n) {τ₀ : ℍ}
    (hM : M.1 0 0 * (τ₀ : ℂ) + M.1 0 1 = (M.1 1 0 * τ₀ + M.1 1 1) * τ₀) :
    IsIntegral ℤ (modularJ τ₀) := by sorry
