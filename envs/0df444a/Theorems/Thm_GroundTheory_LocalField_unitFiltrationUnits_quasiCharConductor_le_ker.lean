-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitFiltrationUnits_quasiCharConductor_le_ker
-- name    : GroundTheory.LocalField.unitFiltrationUnits_quasiCharConductor_le_ker
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:58.869246+00:00
-- url     : https://prove2.me/theorems/ee422524-102f-58f2-975a-79ac12477959
-- title:
--   Local Field: unit Filtration Units quasi Char Conductor le ker
-- statement:
--   The Local Field construction uses the unit Filtration Units quasi Char Conductor le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (χ : Kˣ →* ℂˣ)
variable {χ}
variable (hχ : Continuous χ)
include hχ

theorem GroundTheory.LocalField.unitFiltrationUnits_quasiCharConductor_le_ker :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker := by sorry
