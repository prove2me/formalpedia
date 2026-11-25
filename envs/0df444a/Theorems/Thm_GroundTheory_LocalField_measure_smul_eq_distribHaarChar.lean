-- Prove2me | Theorems.Thm_GroundTheory_LocalField_measure_smul_eq_distribHaarChar
-- name    : GroundTheory.LocalField.measure_smul_eq_distribHaarChar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:59.896683+00:00
-- url     : https://prove2.me/theorems/69df13fb-01fd-4fac-93c8-cc3424afea10
-- title:
--   Local Field: measure smul eq distrib Haar Char
-- statement:
--   The Local Field construction uses the measure smul eq distrib Haar Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L285-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L285-L287

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
variable (μ : Measure K) [μ.IsAddHaarMeasure]

theorem GroundTheory.LocalField.measure_smul_eq_distribHaarChar {c : K} (hc : c ≠ 0) (s : Set K) :
    μ (c • s) = distribHaarChar K (Units.mk0 c hc) * μ s := by sorry
