-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_glue
-- name    : GlobalTheory.RootEx.Exchange.integral_glue
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:14.94853+00:00
-- url     : https://prove2.me/theorems/6e6aae21-3acc-4a6b-851f-1bdba0803094
-- title:
--   Exchange: integral glue
-- statement:
--   The Exchange construction uses the integral glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L66-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L66-L125

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

theorem GlobalTheory.RootEx.Exchange.integral_glue {I B : Type} [Fintype B] (P Q : I → Prop) [Fintype {i // P i}] [Fintype {i // Q i}]
    (j : B → I) (hj : Function.Injective j) (hPj : ∀ b, ¬ P (j b)) (hQ : ∀ i, Q i ↔ P i ∨ ∃ b, j b = i)
    (g : (B → k) → I → k) (hg1 : ∀ u b, g u (j b) = u b) (hg2 : ∀ u i, (∀ b, j b ≠ i) → g u i = 0)
    (f : (I → k) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∫ u : B → k, (∫ e, f (ext0 P e + g u) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) =
      ∫ e, f (ext0 Q e) ∂(Measure.pi fun _ => ν) := by sorry
