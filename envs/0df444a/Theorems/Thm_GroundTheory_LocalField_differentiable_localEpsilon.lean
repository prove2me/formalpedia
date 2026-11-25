-- Prove2me | Theorems.Thm_GroundTheory_LocalField_differentiable_localEpsilon
-- name    : GroundTheory.LocalField.differentiable_localEpsilon
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:23.071177+00:00
-- url     : https://prove2.me/theorems/c7af8ef6-13c5-5486-bcc1-25de60d89c7a
-- title:
--   Local Field: differentiable local Epsilon
-- statement:
--   The Local Field construction uses the differentiable local Epsilon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L95-L98

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

theorem GroundTheory.LocalField.differentiable_localEpsilon : Differentiable ℂ (localEpsilon χ ψ) := by sorry
