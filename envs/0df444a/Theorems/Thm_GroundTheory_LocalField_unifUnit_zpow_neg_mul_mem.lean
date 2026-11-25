-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unifUnit_zpow_neg_mul_mem
-- name    : GroundTheory.LocalField.unifUnit_zpow_neg_mul_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:28.528194+00:00
-- url     : https://prove2.me/theorems/0a187b98-5ed3-4f64-a966-90309ec4f886
-- title:
--   Local Field: unif Unit zpow neg mul mem
-- statement:
--   The Local Field construction uses the unif Unit zpow neg mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L15-L18

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

theorem GroundTheory.LocalField.unifUnit_zpow_neg_mul_mem (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by sorry
