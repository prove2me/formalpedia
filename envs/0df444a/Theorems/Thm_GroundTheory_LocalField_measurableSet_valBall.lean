-- Prove2me | Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
-- name    : GroundTheory.LocalField.measurableSet_valBall
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:00.367598+00:00
-- url     : https://prove2.me/theorems/bf404c5a-c5ff-4cc4-b1db-0452c1308505
-- title:
--   Local Field: measurable Set val Ball
-- statement:
--   The Local Field construction uses the measurable Set val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L231-L232

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.measurableSet_valBall (n : ℤ) : MeasurableSet (valBall K n : Set K) := by sorry
