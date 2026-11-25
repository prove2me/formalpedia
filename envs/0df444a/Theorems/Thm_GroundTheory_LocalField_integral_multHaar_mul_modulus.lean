-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integral_multHaar_mul_modulus
-- name    : GroundTheory.LocalField.integral_multHaar_mul_modulus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:41.764548+00:00
-- url     : https://prove2.me/theorems/81306a08-e31b-5a95-b690-e9ece302ba15
-- title:
--   Local Field: integral mult Haar mul modulus
-- statement:
--   The Local Field construction uses the integral mult Haar mul modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L66-L77

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
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
  [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.integral_multHaar_mul_modulus (h : K → ℂ) :
    ∫ u, h u * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      (multHaarConst K).toReal * ∫ x, h x ∂haarIntegers K := by sorry
