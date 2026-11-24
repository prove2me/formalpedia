-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_flatIntegrable_of_isTensor
-- name    : GlobalTheory.FunObj.flatIntegrable_of_isTensor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:42.156271+00:00
-- url     : https://prove2.me/theorems/40d78674-0381-48f9-a8b5-d5116f2ea00b
-- title:
--   Fun Obj: flat Integrable of is Tensor
-- statement:
--   The Fun Obj construction uses the flat Integrable of is Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L114-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

theorem GlobalTheory.FunObj.flatIntegrable_of_isTensor [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by sorry
