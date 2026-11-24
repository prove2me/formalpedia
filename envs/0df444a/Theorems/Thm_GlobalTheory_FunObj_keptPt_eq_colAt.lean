-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_keptPt_eq_colAt
-- name    : GlobalTheory.FunObj.keptPt_eq_colAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:35:54.916805+00:00
-- url     : https://prove2.me/theorems/23220e27-7bcf-41fd-bf9f-53a3aec5802c
-- title:
--   Fun Obj: kept Pt eq col At
-- statement:
--   The Fun Obj construction uses the kept Pt eq col At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L54-L65

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

theorem GlobalTheory.FunObj.keptPt_eq_colAt (hc : Even c) (w : KeptVar n c n' → k) :
    keptPt w = colAt n' c (c / 2 + 1) fun r => w (colIx hc r) := by sorry
