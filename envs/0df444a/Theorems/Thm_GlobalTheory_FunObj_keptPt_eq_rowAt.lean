-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_keptPt_eq_rowAt
-- name    : GlobalTheory.FunObj.keptPt_eq_rowAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:27.068863+00:00
-- url     : https://prove2.me/theorems/86cba745-8dc4-4f7e-a9f8-d4d0b4f57083
-- title:
--   Fun Obj: kept Pt eq row At
-- statement:
--   The Fun Obj construction uses the kept Pt eq row At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L67-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L67-L78

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
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem GlobalTheory.FunObj.keptPt_eq_rowAt (hc : Odd c) (w : KeptVar n c n' → k) :
    keptPt w = rowAt n c (c / 2 + 1) fun s => w (rowIx hc s) := by sorry
