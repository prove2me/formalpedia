-- Prove2me | Theorems.Thm_GlobalTheory_T_flatTensor_movedTensor_finset_sum_linear
-- name    : GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:16.354562+00:00
-- url     : https://prove2.me/theorems/bf639b95-8ca7-5076-9984-b36abda55e60
-- title:
--   T: flat Tensor moved Tensor finset sum linear
-- statement:
--   The T construction uses the flat Tensor moved Tensor finset sum linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorMovedTensorFinsetSumLinearStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorMovedTensorFinsetSumLinearStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by sorry
