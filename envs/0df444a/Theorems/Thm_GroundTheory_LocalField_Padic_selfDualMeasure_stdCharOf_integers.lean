-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_selfDualMeasure_stdCharOf_integers
-- name    : GroundTheory.LocalField.Padic.selfDualMeasure_stdCharOf_integers
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:58.402815+00:00
-- url     : https://prove2.me/theorems/5af49a5e-c0ce-58ba-8a74-12dcc673ae57
-- title:
--   Padic: self Dual Measure std Char Of integers
-- statement:
--   The Padic construction uses the self Dual Measure std Char Of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L255-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L255-L261

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

theorem GroundTheory.LocalField.Padic.selfDualMeasure_stdCharOf_integers :
    selfDualMeasure (stdCharOf p K) (𝒪[K] : Set K) =
      ((Nat.card (𝒪[K] ⧸ differentIdeal 𝒪[ℚ_[p]] 𝒪[K]) : ℝ≥0) ^ (-(1 / 2 : ℝ)) : ℝ≥0) := by sorry
