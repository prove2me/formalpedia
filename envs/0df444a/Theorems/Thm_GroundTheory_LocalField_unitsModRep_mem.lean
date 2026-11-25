-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsModRep_mem
-- name    : GroundTheory.LocalField.unitsModRep_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:45.55422+00:00
-- url     : https://prove2.me/theorems/58e8a289-94f1-58f4-96c0-8fb1031270eb
-- title:
--   Local Field: units Mod Rep mem
-- statement:
--   The Local Field construction uses the units Mod Rep mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L33-L35

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
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

theorem GroundTheory.LocalField.unitsModRep_mem {c : ℕ} (t : unitsModFiltration K c) :
    unitsModRep t ∈ unitFiltrationUnits K 0 := by sorry
