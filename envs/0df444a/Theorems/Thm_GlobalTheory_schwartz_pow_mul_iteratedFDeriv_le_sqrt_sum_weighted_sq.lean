-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq
-- name    : GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:51.15+00:00
-- url     : https://prove2.me/theorems/b6a52578-b6f1-4116-b3d7-04d266b276e7
-- title:
--   Global Theory: schwartz pow mul iterated FDeriv le sqrt sum weighted sq
-- statement:
--   The Global Theory construction uses the schwartz pow mul iterated FDeriv le sqrt sum weighted sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormL2Bound.lean#L14-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormL2Bound.lean#L14-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormL2Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by sorry
