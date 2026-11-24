-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integrable_row
-- name    : GlobalTheory.FunObj.integrable_row
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:37.394809+00:00
-- url     : https://prove2.me/theorems/3d70bba6-31ad-4202-ab9f-7ca9396fe0b2
-- title:
--   Fun Obj: integrable row
-- statement:
--   The Fun Obj construction uses the integrable row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L222-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L222-L231

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
omit [DecidableEq n] [DecidableEq n'']

theorem GlobalTheory.FunObj.integrable_row {Ψ : Matrix (n'' ⊕ Unit) n k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n'' n k) :
    Integrable (fun u : n → k => Ψ (fromRows x (Matrix.of fun _ => u))) (Measure.pi fun _ => ν) := by sorry
