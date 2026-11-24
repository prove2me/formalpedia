-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_four_indicator
-- name    : GlobalTheory.KSp.FourInv.four_indicator
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:18.837431+00:00
-- url     : https://prove2.me/theorems/0d9e611b-6e0b-400c-ab13-d6c9b38c5476
-- title:
--   Four Inv: four indicator
-- statement:
--   The Four Inv construction uses the four indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L120-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L120-L136

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

theorem GlobalTheory.KSp.FourInv.four_indicator (he : IsPair e) (L : AddSubgroup X) (ho : IsOpen (L : Set X)) (x : X) :
    four μ e ((L : Set X).indicator fun _ => (1 : ℂ)) x =
      (ann he L : Set X).indicator (fun _ => (μ.real (L : Set X) : ℂ)) x := by sorry
