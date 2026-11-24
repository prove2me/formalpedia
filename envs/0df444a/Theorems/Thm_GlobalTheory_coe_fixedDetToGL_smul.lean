-- Prove2me | Theorems.Thm_GlobalTheory_coe_fixedDetToGL_smul
-- name    : GlobalTheory.coe_fixedDetToGL_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:19.785694+00:00
-- url     : https://prove2.me/theorems/5163289a-4dfa-4482-ab19-2683aeb4ee8a
-- title:
--   Global Theory: coe fixed Det To GL smul
-- statement:
--   The Global Theory construction uses the coe fixed Det To GL smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L169-L175

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

theorem GlobalTheory.coe_fixedDetToGL_smul {n : ℕ} (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) (τ : ℍ) :
    ((fixedDetToGL hn A • τ : ℍ) : ℂ) = (A.1 0 0 * τ + A.1 0 1) / (A.1 1 0 * τ + A.1 1 1) := by sorry
