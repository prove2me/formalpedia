-- Prove2me | Theorems.Thm_GlobalTheory_KSp_four_four
-- name    : GlobalTheory.KSp.four_four
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:12.124813+00:00
-- url     : https://prove2.me/theorems/9679821c-8b75-4f3b-9dc1-f5143bf15ce8
-- title:
--   KSp: four four
-- statement:
--   The KSp construction uses the four four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L262-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L262-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
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
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp
open FourInv

theorem GlobalTheory.KSp.four_four (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (hX : Good X)
    (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by sorry
