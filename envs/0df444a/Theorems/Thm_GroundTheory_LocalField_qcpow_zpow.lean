-- Prove2me | Theorems.Thm_GroundTheory_LocalField_qcpow_zpow
-- name    : GroundTheory.LocalField.qcpow_zpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:02.707605+00:00
-- url     : https://prove2.me/theorems/dfd36d77-aa63-5b02-b7f7-1c2ffd173654
-- title:
--   Local Field: qcpow zpow
-- statement:
--   The Local Field construction uses the qcpow zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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

theorem GroundTheory.LocalField.qcpow_zpow (z : ℂ) (n : ℤ) :
    ((residueCard K : ℂ) ^ z) ^ n = (residueCard K : ℂ) ^ ((n : ℂ) * z) := by sorry
