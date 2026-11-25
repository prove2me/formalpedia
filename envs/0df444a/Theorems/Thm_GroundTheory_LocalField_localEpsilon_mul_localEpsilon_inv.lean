-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_mul_localEpsilon_inv
-- name    : GroundTheory.LocalField.localEpsilon_mul_localEpsilon_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:46.323512+00:00
-- url     : https://prove2.me/theorems/63003ba5-e78c-5713-bd8b-a82cde58419f
-- title:
--   Local Field: local Epsilon mul local Epsilon inv
-- statement:
--   The Local Field construction uses the local Epsilon mul local Epsilon inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L232-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L232-L249

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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem GroundTheory.LocalField.localEpsilon_mul_localEpsilon_inv (s : ℂ) :
    localEpsilon χ ψ s * localEpsilon χ⁻¹ (ψ.mulShift (-1)) (1 - s) = 1 := by sorry
