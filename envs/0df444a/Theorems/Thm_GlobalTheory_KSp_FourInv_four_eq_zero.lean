-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_four_eq_zero
-- name    : GlobalTheory.KSp.FourInv.four_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:48.520878+00:00
-- url     : https://prove2.me/theorems/33db18c1-6839-4c53-8872-f905b5ea3e39
-- title:
--   Four Inv: four eq zero
-- statement:
--   The Four Inv construction uses the four eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L103-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L103-L118

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
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem GlobalTheory.KSp.FourInv.four_eq_zero (he : IsPair e) {M : Set X} {f : X → ℂ}
    (hs : ∀ t ∈ M, ∀ x, f (x + t) = f x) {y : X} (hy : y ∉ ann he M) : four μ e f y = 0 := by sorry
