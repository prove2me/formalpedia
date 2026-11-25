-- Prove2me | Theorems.Thm_GroundTheory_LocalField_qpow_ne_zero
-- name    : GroundTheory.LocalField.qpow_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:00.411566+00:00
-- url     : https://prove2.me/theorems/75639908-f615-5d68-94c9-5c9bb645a67e
-- title:
--   Local Field: qpow ne zero
-- statement:
--   The Local Field construction uses the qpow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L219-L221

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

theorem GroundTheory.LocalField.qpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by sorry
