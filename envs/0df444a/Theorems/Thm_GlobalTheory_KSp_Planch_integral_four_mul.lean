-- Prove2me | Theorems.Thm_GlobalTheory_KSp_Planch_integral_four_mul
-- name    : GlobalTheory.KSp.Planch.integral_four_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:40.887955+00:00
-- url     : https://prove2.me/theorems/5dc785b7-6e15-41fe-b943-a42951ae2344
-- title:
--   Planch: integral four mul
-- statement:
--   The Planch construction uses the integral four mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralFourSq.lean#L36-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralFourSq.lean#L36-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
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
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Planch
variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

theorem GlobalTheory.KSp.Planch.integral_four_mul (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (hG : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) (C : ℝ) (_hC : 0 < C)
    (hinv : ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) (φ : X → ℂ) (hφ : φ ∈ SB X) :
    ∫ x, four μ e φ x * starRingEnd ℂ (four μ e φ x) ∂μ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by sorry
