-- Prove2me | Theorems.Thm_GroundTheory_LocalField_multHaar_unitFiltrationUnits_lt_top
-- name    : GroundTheory.LocalField.multHaar_unitFiltrationUnits_lt_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:21.887737+00:00
-- url     : https://prove2.me/theorems/1eab6640-62a2-55d1-8e5b-6a5f2823b069
-- title:
--   Local Field: mult Haar unit Filtration Units lt top
-- statement:
--   The Local Field construction uses the mult Haar unit Filtration Units lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L78-L82

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
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

theorem GroundTheory.LocalField.multHaar_unitFiltrationUnits_lt_top (c : ℕ) :
    multHaar K (unitFiltrationUnits K c) < ∞ := by sorry
