-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_unitsModCoset_mk
-- name    : GroundTheory.LocalField.mem_unitsModCoset_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:20:11.756667+00:00
-- url     : https://prove2.me/theorems/d39e0d70-6337-5e3b-b228-76bfc478a1ac
-- title:
--   Local Field: mem units Mod Coset mk
-- statement:
--   The Local Field construction uses the mem units Mod Coset mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L43-L47

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

theorem GroundTheory.LocalField.mem_unitsModCoset_mk {c : ℕ} {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 0) :
    x ∈ unitsModCoset (QuotientGroup.mk ⟨x, hx⟩ : unitsModFiltration K c) := by sorry
