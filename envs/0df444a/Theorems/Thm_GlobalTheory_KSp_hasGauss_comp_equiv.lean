-- Prove2me | Theorems.Thm_GlobalTheory_KSp_hasGauss_comp_equiv
-- name    : GlobalTheory.KSp.hasGauss_comp_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:52.0172+00:00
-- url     : https://prove2.me/theorems/cdf17e8f-c870-4964-8325-efb614bb2e64
-- title:
--   KSp: has Gauss comp equiv
-- statement:
--   The KSp construction uses the has Gauss comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasGaussIntegralCompAddEquivRescale.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasGaussIntegralCompAddEquivRescale.lean#L11-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompAddEquivRescale
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
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.hasGauss_comp_equiv (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y)
    (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ) (hμ : μ.map T = r • μ') (h : HasGauss μ' f γ) :
    HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by sorry
