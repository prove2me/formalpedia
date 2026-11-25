-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_selfDualMeasure_stdCharOf_integers_eq_rpow
-- name    : GroundTheory.LocalField.Padic.selfDualMeasure_stdCharOf_integers_eq_rpow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:28.986416+00:00
-- url     : https://prove2.me/theorems/6c68f943-afab-5984-a91b-e6648095297f
-- title:
--   Padic: self Dual Measure std Char Of integers eq rpow
-- statement:
--   The Padic construction uses the self Dual Measure std Char Of integers eq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L248-L253

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
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
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.Padic.selfDualMeasure_stdCharOf_integers_eq_rpow :
    selfDualMeasure (stdCharOf p K) (𝒪[K] : Set K) =
      ((residueCard K : ℝ≥0) ^ (-(differentExponent ℚ_[p] K : ℝ) / 2) : ℝ≥0) := by sorry
