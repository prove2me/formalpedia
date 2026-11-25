-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_mulShift
-- name    : GroundTheory.LocalField.localEpsilon_mulShift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:19.059803+00:00
-- url     : https://prove2.me/theorems/1b50646f-239f-5aba-b46c-2be761396a57
-- title:
--   Local Field: local Epsilon mul Shift
-- statement:
--   The Local Field construction uses the local Epsilon mul Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L100-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L100-L173

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem GroundTheory.LocalField.localEpsilon_mulShift (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (a : Kˣ) (s : ℂ) :
    localEpsilon χ (ψ.mulShift (a : K)) s =
      ((χ a : ℂˣ) : ℂ) * ((modulus (a : K) : ℝ) : ℂ) ^ (s - 1 / 2) * localEpsilon χ ψ s := by sorry
