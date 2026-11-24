-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_indicator_mem
-- name    : GlobalTheory.KSp.FourInv.indicator_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:42.422272+00:00
-- url     : https://prove2.me/theorems/48f3a3a2-7214-46b4-97ff-93d4920d9ee3
-- title:
--   Four Inv: indicator mem
-- statement:
--   The Four Inv construction uses the indicator mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L88-L99

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

theorem GlobalTheory.KSp.FourInv.indicator_mem [IsTopologicalAddGroup X] [T2Space X] (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) : (L : Set X).indicator (fun _ => (1 : ℂ)) ∈ SB X := by sorry
