-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsMeasureOf_eq
-- name    : GroundTheory.LocalField.unitsMeasureOf_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:10.33051+00:00
-- url     : https://prove2.me/theorems/b96c2325-1bd3-5a70-8150-26da27a592c4
-- title:
--   Local Field: units Measure Of eq
-- statement:
--   The Local Field construction uses the units Measure Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L39-L44

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
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
open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.unitsMeasureOf_eq (μ : Measure K) [μ.IsAddHaarMeasure] :
    unitsMeasureOf μ = ((1 - ((residueCard K : ℝ≥0∞))⁻¹) * μ (𝒪[K] : Set K)) • multHaar K := by sorry
