-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_smul_haarIntegers
-- name    : GroundTheory.LocalField.eq_smul_haarIntegers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:00.82193+00:00
-- url     : https://prove2.me/theorems/146ee314-cf82-40a0-b022-b87c9c92ce3c
-- title:
--   Local Field: eq smul haar Integers
-- statement:
--   The Local Field construction uses the eq smul haar Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L392-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L392-L396

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]

theorem GroundTheory.LocalField.eq_smul_haarIntegers (ν : Measure K) [ν.IsAddHaarMeasure] :
    ν = ν (𝒪[K] : Set K) • haarIntegers K := by sorry
