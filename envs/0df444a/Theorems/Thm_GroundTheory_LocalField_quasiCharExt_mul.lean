-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiCharExt_mul
-- name    : GroundTheory.LocalField.quasiCharExt_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:46.24838+00:00
-- url     : https://prove2.me/theorems/bfed3035-e057-4d0c-8997-c1ccde0e5132
-- title:
--   Local Field: quasi Char Ext mul
-- statement:
--   The Local Field construction uses the quasi Char Ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L43-L53

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.quasiCharExt_mul (χ : Kˣ →* ℂˣ) (x y : K) :
    quasiCharExt χ (x * y) = quasiCharExt χ x * quasiCharExt χ y := by sorry
