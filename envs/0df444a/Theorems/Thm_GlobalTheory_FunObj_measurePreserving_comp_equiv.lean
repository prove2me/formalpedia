-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_measurePreserving_comp_equiv
-- name    : GlobalTheory.FunObj.measurePreserving_comp_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:54.00507+00:00
-- url     : https://prove2.me/theorems/4d1cf887-7dd9-4362-921b-a0c2e4c18fc2
-- title:
--   Fun Obj: measure Preserving comp equiv
-- statement:
--   The Fun Obj construction uses the measure Preserving comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L203-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L203-L205

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
omit [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure]

theorem GlobalTheory.FunObj.measurePreserving_comp_equiv {A B : Type} [Fintype A] [Fintype B] [SigmaFinite ν] (e : A ≃ B) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : B => k) e).symm (Measure.pi fun _ => ν)
      (Measure.pi fun _ => ν) := by sorry
