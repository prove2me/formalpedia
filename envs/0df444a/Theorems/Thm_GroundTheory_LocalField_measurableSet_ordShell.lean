-- Prove2me | Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell
-- name    : GroundTheory.LocalField.measurableSet_ordShell
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:28.577477+00:00
-- url     : https://prove2.me/theorems/448215c9-a1a0-5f3b-be48-cb3e2af8128c
-- title:
--   Local Field: measurable Set ord Shell
-- statement:
--   The Local Field construction uses the measurable Set ord Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L113-L121

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
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

theorem GroundTheory.LocalField.measurableSet_ordShell (k : ℤ) : MeasurableSet (ordShell K k) := by sorry
