-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_double_step
-- name    : GlobalTheory.FunObj.integral_double_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:21.225277+00:00
-- url     : https://prove2.me/theorems/3aca29a1-81ae-4741-b3ac-900e159d0a51
-- title:
--   Fun Obj: integral double step
-- statement:
--   The Fun Obj construction uses the integral double step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L251-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L251-L267

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
open Classical

theorem GlobalTheory.FunObj.integral_double_step (hψ : Continuous ψ) {c c' : ℕ} (hc : Even c) (hc' : Odd c')
    {Φ₁ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {Φ₂ : Matrix (n'' ⊕ Fin c') (n ⊕ Fin (c' + 1)) k → ℂ}
    (h₁ : Φ₁ ∈ SB _) (h₂ : Φ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (KeptVar n c n' → k) × (KeptVar n'' c' n → k), flatStep ψ ν Φ₁ x₁ p.1 * flatStep ψ ν Φ₂ x₂ p.2 *
      (ψ (-∑ r, p.2 (rowIx hc' r) * p.1 (colIx hc r)) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν (flCol ψ ν (c / 2 + 1) Φ₁) (flRow ψ ν (c' / 2 + 1) Φ₂) (x₁, x₂) := by sorry
