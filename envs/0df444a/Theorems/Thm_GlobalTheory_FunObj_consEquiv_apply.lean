-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_consEquiv_apply
-- name    : GlobalTheory.FunObj.consEquiv_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:48.755819+00:00
-- url     : https://prove2.me/theorems/f1b04d19-58b4-4ab0-a982-7cc5c21b2536
-- title:
--   Fun Obj: cons Equiv apply
-- statement:
--   The Fun Obj construction uses the cons Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L101-L103

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

theorem GlobalTheory.FunObj.consEquiv_apply {n : ℕ} (E : Fin (n + 1) → Type) [∀ j, MeasurableSpace (E j)]
    (p : E 0 × ∀ j : Fin n, E j.succ) : consEquiv E p = Fin.cons p.1 p.2 := by sorry
