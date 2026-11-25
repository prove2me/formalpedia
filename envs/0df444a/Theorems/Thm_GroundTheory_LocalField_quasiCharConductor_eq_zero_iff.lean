-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiCharConductor_eq_zero_iff
-- name    : GroundTheory.LocalField.quasiCharConductor_eq_zero_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:55.165366+00:00
-- url     : https://prove2.me/theorems/4fc7e30e-c86e-4692-887c-bc18c6afaa77
-- title:
--   Local Field: quasi Char Conductor eq zero iff
-- statement:
--   The Local Field construction uses the quasi Char Conductor eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L81-L87

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
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

theorem GroundTheory.LocalField.quasiCharConductor_eq_zero_iff : quasiCharConductor χ = 0 ↔ IsUnramifiedChar χ := by sorry
