-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiCharConductor_pos
-- name    : GroundTheory.LocalField.quasiCharConductor_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:13.417879+00:00
-- url     : https://prove2.me/theorems/ec53ced1-f5bb-42de-97b2-d9939c38500d
-- title:
--   Local Field: quasi Char Conductor pos
-- statement:
--   The Local Field construction uses the quasi Char Conductor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L99-L101

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

theorem GroundTheory.LocalField.quasiCharConductor_pos (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ := by sorry
