-- Prove2me | Theorems.Thm_GroundTheory_LocalField_zpowers_mk_uniformizerUnit
-- name    : GroundTheory.LocalField.zpowers_mk_uniformizerUnit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:30:52.751158+00:00
-- url     : https://prove2.me/theorems/41b6b65e-39b8-4ebf-b02e-976f02d6e813
-- title:
--   Local Field: zpowers mk uniformizer Unit
-- statement:
--   The Local Field construction uses the zpowers mk uniformizer Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedNormSurj.lean#L273-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedNormSurj.lean#L273-L286

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Theorems.Thm_GroundTheory_Global_div_mem_unitFiltration_iff
import Theorems.Thm_GroundTheory_Global_filtrationComplete_unitFiltration
import Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsUnramified K L]

theorem GroundTheory.LocalField.zpowers_mk_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Subgroup.zpowers (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) = ⊤ := by sorry
