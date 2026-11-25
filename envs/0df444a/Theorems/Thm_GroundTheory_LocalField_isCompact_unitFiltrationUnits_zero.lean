-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isCompact_unitFiltrationUnits_zero
-- name    : GroundTheory.LocalField.isCompact_unitFiltrationUnits_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:26.64387+00:00
-- url     : https://prove2.me/theorems/5c790e51-6a93-457d-9aac-5d31b57cb7b5
-- title:
--   Local Field: is Compact unit Filtration Units zero
-- statement:
--   The Local Field construction uses the is Compact unit Filtration Units zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L24-L39

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

theorem GroundTheory.LocalField.isCompact_unitFiltrationUnits_zero :
    IsCompact (unitFiltrationUnits K 0 : Set Kˣ) := by sorry
