-- Prove2me | Theorems.Thm_GlobalTheory_SetIntegralSmoothness_contDiff_setIntegral
-- name    : GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:08.849141+00:00
-- url     : https://prove2.me/theorems/e0e2c4e7-7399-4e5b-a16d-3451f562db58
-- title:
--   Set Integral Smoothness: cont Diff set Integral
-- statement:
--   The Set Integral Smoothness construction uses the cont Diff set Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasFDerivAtSetIntegral.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HasFDerivAtSetIntegral.lean#L40-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasFDerivAtSetIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ContDiff
open GlobalTheory GlobalTheory.SetIntegralSmoothness

theorem GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ) := by sorry
