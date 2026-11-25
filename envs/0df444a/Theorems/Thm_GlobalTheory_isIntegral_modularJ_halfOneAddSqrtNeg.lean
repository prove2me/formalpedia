-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_modularJ_halfOneAddSqrtNeg
-- name    : GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:50.429971+00:00
-- url     : https://prove2.me/theorems/5f7f2948-27e9-4e66-b456-0265ad1edd0b
-- title:
--   Global Theory: is Integral modular J half One Add Sqrt Neg
-- statement:
--   The Global Theory construction uses the is Integral modular J half One Add Sqrt Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L319-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L319-L326

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

theorem GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg (d : ℕ) (hd : d ≠ 0) :
    IsIntegral ℤ (modularJ (halfOneAddSqrtNeg d hd)) := by sorry
