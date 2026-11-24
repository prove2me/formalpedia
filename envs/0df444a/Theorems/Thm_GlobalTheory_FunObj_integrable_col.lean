-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integrable_col
-- name    : GlobalTheory.FunObj.integrable_col
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:51.426519+00:00
-- url     : https://prove2.me/theorems/5fa4af24-91d1-40a4-bfb3-6dfbfb95a35f
-- title:
--   Fun Obj: integrable col
-- statement:
--   The Fun Obj construction uses the integrable col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L209-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L209-L218

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
omit [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.FunObj.integrable_col {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n n' k) :
    Integrable (fun y : n → k => Ψ (fromCols x (Matrix.of fun r _ => y r))) (Measure.pi fun _ => ν) := by sorry
