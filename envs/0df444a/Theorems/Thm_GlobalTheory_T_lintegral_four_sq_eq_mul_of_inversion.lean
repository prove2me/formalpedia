-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_four_sq_eq_mul_of_inversion
-- name    : GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:21.195681+00:00
-- url     : https://prove2.me/theorems/cb26f758-4eef-4b72-9640-a02fc835a427
-- title:
--   T: lintegral four sq eq mul of inversion
-- statement:
--   The T construction uses the lintegral four sq eq mul of inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralFourSqStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralFourSqStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by sorry
