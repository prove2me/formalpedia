-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_multHaarOf_selfDualMeasure_stdCharOf_units
-- name    : GroundTheory.LocalField.Padic.multHaarOf_selfDualMeasure_stdCharOf_units
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:09.07655+00:00
-- url     : https://prove2.me/theorems/23c973b1-d497-5b80-a4c3-c6e4573d3be8
-- title:
--   Padic: mult Haar Of self Dual Measure std Char Of units
-- statement:
--   The Padic construction uses the mult Haar Of self Dual Measure std Char Of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierMult.lean#L76-L79

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
open GroundTheory.LocalField.Padic
variable (p : ℕ) [Fact p.Prime] (K) [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.LocalField.Padic.multHaarOf_selfDualMeasure_stdCharOf_units :
    multHaarOf (selfDualMeasure (stdCharOf p K)) (unitFiltrationUnits K 0 : Set Kˣ) =
      ((Nat.card (𝒪[K] ⧸ differentIdeal 𝒪[ℚ_[p]] 𝒪[K]) : ℝ≥0) ^ (-(1 / 2 : ℝ)) : ℝ≥0) := by sorry
