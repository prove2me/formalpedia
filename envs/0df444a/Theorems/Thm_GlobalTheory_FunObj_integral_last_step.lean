-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_last_step
-- name    : GlobalTheory.FunObj.integral_last_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:36.278067+00:00
-- url     : https://prove2.me/theorems/43d7d4d8-5291-41f7-85d7-d8808eee5e8e
-- title:
--   Fun Obj: integral last step
-- statement:
--   The Fun Obj construction uses the integral last step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L271-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L271-L278

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

theorem GlobalTheory.FunObj.integral_last_step {c : ℕ} (hc : Even c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k)
    (z : n → k) :
    ∫ w : KeptVar n c n' → k, flatStep ψ ν Φ x w * (ψ (-∑ r, z r * w (colIx hc r)) : ℂ) ∂(Measure.pi fun _ => ν) =
      GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν (c / 2 + 1) Φ (fromCols x (Matrix.of fun r _ => u r))) z := by sorry
