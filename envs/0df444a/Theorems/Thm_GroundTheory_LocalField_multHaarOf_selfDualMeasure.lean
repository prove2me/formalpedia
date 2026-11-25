-- Prove2me | Theorems.Thm_GroundTheory_LocalField_multHaarOf_selfDualMeasure
-- name    : GroundTheory.LocalField.multHaarOf_selfDualMeasure
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:55.60529+00:00
-- url     : https://prove2.me/theorems/26dd8db4-022a-516a-9a38-518dbcdae1a7
-- title:
--   Local Field: mult Haar Of self Dual Measure
-- statement:
--   The Local Field construction uses the mult Haar Of self Dual Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L60-L63

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

theorem GroundTheory.LocalField.multHaarOf_selfDualMeasure (ψ : AddChar K Circle) :
    multHaarOf (selfDualMeasure ψ) =
      (((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) : ℝ≥0∞) • multHaar K := by sorry
