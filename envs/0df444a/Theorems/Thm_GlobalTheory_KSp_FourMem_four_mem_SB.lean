-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourMem_four_mem_SB
-- name    : GlobalTheory.KSp.FourMem.four_mem_SB
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:29.442962+00:00
-- url     : https://prove2.me/theorems/5b92e528-3daf-4cff-9d7c-67218e4b274d
-- title:
--   Four Mem: four mem SB
-- statement:
--   The Four Mem construction uses the four mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformMemSchwartzBruhat.lean#L32-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformMemSchwartzBruhat.lean#L32-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhat
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
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourMem

theorem GlobalTheory.KSp.FourMem.four_mem_SB : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by sorry
