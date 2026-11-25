-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residueCard_nnreal_ne_zero
-- name    : GroundTheory.LocalField.residueCard_nnreal_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:18.275126+00:00
-- url     : https://prove2.me/theorems/3d30d6a0-e41f-41ca-aa73-3c112be986b7
-- title:
--   Local Field: residue Card nnreal ne zero
-- statement:
--   The Local Field construction uses the residue Card nnreal ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L117-L118

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.residueCard_nnreal_ne_zero : (residueCard K : ℝ≥0) ≠ 0 := by sorry
