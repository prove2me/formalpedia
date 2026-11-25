-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiCharExponent_inv
-- name    : GroundTheory.LocalField.quasiCharExponent_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:46.51074+00:00
-- url     : https://prove2.me/theorems/024beda4-c586-42e7-aa94-bc8f7bf89cba
-- title:
--   Local Field: quasi Char Exponent inv
-- statement:
--   The Local Field construction uses the quasi Char Exponent inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L150-L152

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
omit hχ

theorem GroundTheory.LocalField.quasiCharExponent_inv : quasiCharExponent χ⁻¹ = -quasiCharExponent χ := by sorry
