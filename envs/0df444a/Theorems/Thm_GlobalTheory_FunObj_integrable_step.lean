-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integrable_step
-- name    : GlobalTheory.FunObj.integrable_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:55.711954+00:00
-- url     : https://prove2.me/theorems/2d9192f8-8576-4873-a62e-e9d69ddf1fda
-- title:
--   Fun Obj: integrable step
-- statement:
--   The Fun Obj construction uses the integrable step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L168-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [MeasurableSpace k] [BorelSpace k]
open Classical
omit [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.FunObj.integrable_step {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) (x₀ : Matrix n n' k) :
    Integrable (fun e : StepVar n c n' → k => Φ (stepPt x₀ e) * (ψ (-ch (stepPt x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by sorry
