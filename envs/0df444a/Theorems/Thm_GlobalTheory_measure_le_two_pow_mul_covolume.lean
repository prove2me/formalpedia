-- Prove2me | Theorems.Thm_GlobalTheory_measure_le_two_pow_mul_covolume
-- name    : GlobalTheory.measure_le_two_pow_mul_covolume
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:16.677644+00:00
-- url     : https://prove2.me/theorems/e22c1cd6-473d-4bdd-9038-07e5c7a3b656
-- title:
--   Global Theory: measure le two pow mul covolume
-- statement:
--   The Global Theory construction uses the measure le two pow mul covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L17-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.measure_le_two_pow_mul_covolume (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hsymm : ∀ x ∈ s, -x ∈ s) (hconv : Convex ℝ s)
    (hL : ∀ x ∈ L, x ≠ 0 → x ∉ s) :
    μ s ≤ ENNReal.ofReal (2 ^ finrank ℝ E * ZLattice.covolume L μ) := by sorry
