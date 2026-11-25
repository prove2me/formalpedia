-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integral_comp_mul_left
-- name    : GroundTheory.LocalField.integral_comp_mul_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:39.706991+00:00
-- url     : https://prove2.me/theorems/c85cd596-91fe-43b3-b2c8-20095c026bda
-- title:
--   Local Field: integral comp mul left
-- statement:
--   The Local Field construction uses the integral comp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L369-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L369-L375

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

theorem GroundTheory.LocalField.integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : K} (ha : a ≠ 0) (f : K → E) :
    ∫ x, f (a * x) ∂μ = ((modulus a : ℝ))⁻¹ • ∫ x, f x ∂μ := by sorry
