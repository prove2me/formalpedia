-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_isOpen_ann
-- name    : GlobalTheory.KSp.FourInv.isOpen_ann
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:47.718817+00:00
-- url     : https://prove2.me/theorems/4f6c6227-7a1f-407d-977b-a2e36f367d0b
-- title:
--   Four Inv: is Open ann
-- statement:
--   The Four Inv construction uses the is Open ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L38-L52

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

theorem GlobalTheory.KSp.FourInv.isOpen_ann [IsTopologicalAddGroup X] (he : IsPair e) {L : Set X} (hL : IsCompact L) :
    IsOpen (ann he L : Set X) := by sorry
