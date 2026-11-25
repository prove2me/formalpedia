-- Prove2me | Theorems.Thm_GroundTheory_LocalField_one_sub_quasiChar_unifUnit_mul_qpow_ne_zero
-- name    : GroundTheory.LocalField.one_sub_quasiChar_unifUnit_mul_qpow_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:25.930475+00:00
-- url     : https://prove2.me/theorems/ab0bd960-fdda-4691-b95f-b536eab0ccb4
-- title:
--   Local Field: one sub quasi Char unif Unit mul qpow ne zero
-- statement:
--   The Local Field construction uses the one sub quasi Char unif Unit mul qpow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L120-L126

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
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

theorem GroundTheory.LocalField.one_sub_quasiChar_unifUnit_mul_qpow_ne_zero {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by sorry
