-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_pair_eq_contr
-- name    : GlobalTheory.FunObj.integral_pair_eq_contr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:47.748577+00:00
-- url     : https://prove2.me/theorems/0b382f1b-6faa-4536-a921-37dd8f340c58
-- title:
--   Fun Obj: integral pair eq contr
-- statement:
--   The Fun Obj construction uses the integral pair eq contr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L233-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L233-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
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
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.FunObj.integral_pair_eq_contr (hψ : Continuous ψ) {Ψ₁ : Matrix n (n' ⊕ Unit) k → ℂ} {Ψ₂ : Matrix (n'' ⊕ Unit) n k → ℂ}
    (h₁ : Ψ₁ ∈ SB _) (h₂ : Ψ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (n → k) × (n → k), Ψ₁ (fromCols x₁ (Matrix.of fun r _ => p.1 r)) * Ψ₂ (fromRows x₂ (Matrix.of fun _ => p.2)) *
      (ψ (-∑ r, p.2 r * p.1 r) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν Ψ₁ Ψ₂ (x₁, x₂) := by sorry
