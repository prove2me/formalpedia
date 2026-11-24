-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_flatTensor_moved_sum
-- name    : GlobalTheory.FunObj.flatTensor_moved_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:42:16.337819+00:00
-- url     : https://prove2.me/theorems/7b88eecc-aa8f-4841-9221-0ee73cd92b61
-- title:
--   Fun Obj: flat Tensor moved sum
-- statement:
--   The Fun Obj construction uses the flat Tensor moved sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorMovedTensorFinsetSumLinear.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorMovedTensorFinsetSumLinear.lean#L9-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem GlobalTheory.FunObj.flatTensor_moved_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by sorry
