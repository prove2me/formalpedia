-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_shear
-- name    : GlobalTheory.RootEx.Exchange.integral_shear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:47.285149+00:00
-- url     : https://prove2.me/theorems/7ef19b6b-25c4-4d6c-abce-6c237dd2df4c
-- title:
--   Exchange: integral shear
-- statement:
--   The Exchange construction uses the integral shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L17-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L17-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [T2Space k]

theorem GlobalTheory.RootEx.Exchange.integral_shear {I : Type} [Fintype I] (J : I → Prop) (S : (I → k) → (I → k))
    (hS : Continuous S) (h0 : ∀ e i, ¬ J i → S e i = 0)
    (h1 : ∀ e e' : I → k, (∀ i, ¬ J i → e i = e' i) → S e = S e')
    (f : (I → k) → ℂ) (hf : Continuous f) :
    ∫ e, f (e + S e) ∂(Measure.pi fun _ => ν) = ∫ e, f e ∂(Measure.pi fun _ => ν) := by sorry
