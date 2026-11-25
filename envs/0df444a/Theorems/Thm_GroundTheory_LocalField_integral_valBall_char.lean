-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integral_valBall_char
-- name    : GroundTheory.LocalField.integral_valBall_char
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:23.815585+00:00
-- url     : https://prove2.me/theorems/65a41872-8dd1-489a-8dee-5265ac19b30c
-- title:
--   Local Field: integral val Ball char
-- statement:
--   The Local Field construction uses the integral val Ball char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L94-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L94-L121

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
open scoped Classical

theorem GroundTheory.LocalField.integral_valBall_char (χ : AddChar K Circle) (k : ℤ) :
    ∫ x in valBall K k, (χ x : ℂ) ∂μ =
      if IsTrivialOn χ k then (μ.real (valBall K k) : ℂ) else 0 := by sorry
