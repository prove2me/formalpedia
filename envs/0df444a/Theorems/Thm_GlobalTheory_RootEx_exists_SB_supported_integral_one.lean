-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_exists_SB_supported_integral_one
-- name    : GlobalTheory.RootEx.exists_SB_supported_integral_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:26.292149+00:00
-- url     : https://prove2.me/theorems/9e7a0a7c-8ac3-4e57-bb71-20ba582cba5b
-- title:
--   Root Ex: exists SB supported integral one
-- statement:
--   The Root Ex construction uses the exists SB supported integral one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzBruhatSupportedNhdsIntegralOne.lean#L40-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzBruhatSupportedNhdsIntegralOne.lean#L40-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx
open GlobalTheory.SplitWeil.FourierPi

theorem GlobalTheory.RootEx.exists_SB_supported_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by sorry
