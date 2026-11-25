-- Prove2me | Theorems.Thm_GroundTheory_LocalField_measurableSet_unitsModCoset
-- name    : GroundTheory.LocalField.measurableSet_unitsModCoset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:52.191993+00:00
-- url     : https://prove2.me/theorems/cb55754d-ddf9-56b1-acf0-1676835cb266
-- title:
--   Local Field: measurable Set units Mod Coset
-- statement:
--   The Local Field construction uses the measurable Set units Mod Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L70-L72

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

theorem GroundTheory.LocalField.measurableSet_unitsModCoset {c : ℕ} (t : unitsModFiltration K c) :
    MeasurableSet (unitsModCoset t) := by sorry
