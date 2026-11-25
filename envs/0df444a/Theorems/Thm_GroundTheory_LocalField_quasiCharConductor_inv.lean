-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiCharConductor_inv
-- name    : GroundTheory.LocalField.quasiCharConductor_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:18.360697+00:00
-- url     : https://prove2.me/theorems/bd18f95b-4a46-4be9-a4e8-b7c33f471ce8
-- title:
--   Local Field: quasi Char Conductor inv
-- statement:
--   The Local Field construction uses the quasi Char Conductor inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L53-L57

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
variable {χ : Kˣ →* ℂˣ}

theorem GroundTheory.LocalField.quasiCharConductor_inv : quasiCharConductor χ⁻¹ = quasiCharConductor χ := by sorry
