-- Prove2me | Theorems.Thm_GroundTheory_LocalField_multHaarOf_unitFiltrationUnits_zero
-- name    : GroundTheory.LocalField.multHaarOf_unitFiltrationUnits_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:39.286042+00:00
-- url     : https://prove2.me/theorems/dcb7a57c-8124-4e18-8d73-bf8ba6f409d1
-- title:
--   Local Field: mult Haar Of unit Filtration Units zero
-- statement:
--   The Local Field construction uses the mult Haar Of unit Filtration Units zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L56-L58

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

theorem GroundTheory.LocalField.multHaarOf_unitFiltrationUnits_zero (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ (unitFiltrationUnits K 0 : Set Kˣ) = μ (𝒪[K] : Set K) := by sorry
