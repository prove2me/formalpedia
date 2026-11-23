-- Prove2me | Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_mul
-- name    : GlobalTheory.HasUnitLeadingExpansion.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:35.956006+00:00
-- url     : https://prove2.me/theorems/d84318e3-2be0-4722-8886-69f2cc063adb
-- title:
--   Has Unit Leading Expansion: mul
-- statement:
--   The Has Unit Leading Expansion construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ModularJExpansionAndPolynomialAndIsIntegral.lean#L44-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasQExpansion_mul

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

theorem GlobalTheory.HasUnitLeadingExpansion.mul {n : ℝ} {f g : ℍ → ℂ} (hf : HasUnitLeadingExpansion n f)
    (hg : HasUnitLeadingExpansion n g) : HasUnitLeadingExpansion n (f * g) := by sorry
