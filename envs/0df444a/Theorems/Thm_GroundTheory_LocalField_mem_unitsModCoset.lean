-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_unitsModCoset
-- name    : GroundTheory.LocalField.mem_unitsModCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:43.133811+00:00
-- url     : https://prove2.me/theorems/267768da-325d-51e4-a78f-01ce2f52741a
-- title:
--   Local Field: mem units Mod Coset
-- statement:
--   The Local Field construction uses the mem units Mod Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L40-L41

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

theorem GroundTheory.LocalField.mem_unitsModCoset {c : ℕ} {t : unitsModFiltration K c} {x : Kˣ} :
    x ∈ unitsModCoset t ↔ (unitsModRep t)⁻¹ * x ∈ unitFiltrationUnits K c := by sorry
