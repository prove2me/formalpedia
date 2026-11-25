-- Prove2me | Theorems.Thm_GroundTheory_LocalField_multHaar_unitFiltrationUnits_zero
-- name    : GroundTheory.LocalField.multHaar_unitFiltrationUnits_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:53.957302+00:00
-- url     : https://prove2.me/theorems/fe2d4de6-0431-50ff-bee8-a0a217e25381
-- title:
--   Local Field: mult Haar unit Filtration Units zero
-- statement:
--   The Local Field construction uses the mult Haar unit Filtration Units zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L278-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L278-L312

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
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
variable [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.multHaar_unitFiltrationUnits_zero :
    multHaar K (unitFiltrationUnits K 0 : Set Kˣ) = 1 := by sorry
