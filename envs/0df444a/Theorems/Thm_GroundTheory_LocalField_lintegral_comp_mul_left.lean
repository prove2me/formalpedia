-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lintegral_comp_mul_left
-- name    : GroundTheory.LocalField.lintegral_comp_mul_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:58.235413+00:00
-- url     : https://prove2.me/theorems/db29a487-940f-4e88-a186-effa71bc7421
-- title:
--   Local Field: lintegral comp mul left
-- statement:
--   The Local Field construction uses the lintegral comp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L377-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L377-L382

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

theorem GroundTheory.LocalField.lintegral_comp_mul_left {a : K} (ha : a ≠ 0) (f : K → ℝ≥0∞) :
    ∫⁻ x, f (a * x) ∂μ = ((modulus a : ℝ≥0∞))⁻¹ * ∫⁻ x, f x ∂μ := by sorry
