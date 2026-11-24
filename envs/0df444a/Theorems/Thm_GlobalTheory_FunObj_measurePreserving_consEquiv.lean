-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_measurePreserving_consEquiv
-- name    : GlobalTheory.FunObj.measurePreserving_consEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:09.659966+00:00
-- url     : https://prove2.me/theorems/6293e203-f18b-4aae-9f46-fa2be3261d8e
-- title:
--   Fun Obj: measure Preserving cons Equiv
-- statement:
--   The Fun Obj construction uses the measure Preserving cons Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L105-L108

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

theorem GlobalTheory.FunObj.measurePreserving_consEquiv {n : ℕ} {E : Fin (n + 1) → Type} [∀ j, MeasurableSpace (E j)]
    (μ : ∀ j, Measure (E j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (consEquiv E) ((μ 0).prod (Measure.pi fun j => μ j.succ)) (Measure.pi μ) := by sorry
