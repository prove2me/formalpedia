-- Prove2me | Theorems.Thm_GlobalTheory_C_mem_integralSeries
-- name    : GlobalTheory.C_mem_integralSeries
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:52.977466+00:00
-- url     : https://prove2.me/theorems/0e6a5738-0dc1-4a69-a119-ae214febe9b9
-- title:
--   Global Theory: C mem integral Series
-- statement:
--   The Global Theory construction uses the C mem integral Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L26-L29

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

theorem GlobalTheory.C_mem_integralSeries {c : ℂ} (hc : IsIntegral ℤ c) : C c ∈ integralSeries := by sorry
