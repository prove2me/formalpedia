-- Prove2me | Theorems.Thm_GroundTheory_LocalField_selfDualMeasure_integers
-- name    : GroundTheory.LocalField.selfDualMeasure_integers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:14.605119+00:00
-- url     : https://prove2.me/theorems/dd06445a-bfad-4ac1-84ab-c3998d605229
-- title:
--   Local Field: self Dual Measure integers
-- statement:
--   The Local Field construction uses the self Dual Measure integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L29-L32

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
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
variable [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.selfDualMeasure_integers (ψ : AddChar K Circle) :
    selfDualMeasure ψ (𝒪[K] : Set K) = ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) := by sorry
