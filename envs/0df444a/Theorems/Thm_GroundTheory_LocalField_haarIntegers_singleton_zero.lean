-- Prove2me | Theorems.Thm_GroundTheory_LocalField_haarIntegers_singleton_zero
-- name    : GroundTheory.LocalField.haarIntegers_singleton_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:58.029378+00:00
-- url     : https://prove2.me/theorems/d0b7acef-5376-5eba-bec2-0000b2f8a4fb
-- title:
--   Local Field: haar Integers singleton zero
-- statement:
--   The Local Field construction uses the haar Integers singleton zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L51-L64

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

theorem GroundTheory.LocalField.haarIntegers_singleton_zero : haarIntegers K {0} = 0 := by sorry
