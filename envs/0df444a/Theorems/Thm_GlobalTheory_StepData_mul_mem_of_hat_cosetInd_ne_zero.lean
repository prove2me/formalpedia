-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mul_mem_of_hat_cosetInd_ne_zero
-- name    : GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:14.882358+00:00
-- url     : https://prove2.me/theorems/182806b9-c368-4682-a12e-67c1b7746019
-- title:
--   Step Data: mul mem of hat coset Ind ne zero
-- statement:
--   The Step Data construction uses the mul mem of hat coset Ind ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MulMemOfHatCosetIndNeZero.lean#L47-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MulMemOfHatCosetIndNeZero.lean#L47-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.StepData
open MeasureTheory ValuativeRel Matrix

theorem GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by sorry
