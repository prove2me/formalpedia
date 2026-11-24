-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_prod_even_succ_succ
-- name    : GlobalTheory.FunObj.prod_even_succ_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:50.995858+00:00
-- url     : https://prove2.me/theorems/af34167a-46d0-4086-a8d7-65c6b6b11c2d
-- title:
--   Fun Obj: prod even succ succ
-- statement:
--   The Fun Obj construction uses the prod even succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L125-L128

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

theorem GlobalTheory.FunObj.prod_even_succ_succ (n : ℕ) (f : Fin (n + 2) → ℂ) : (∏ j : Fin (n + 2), if Even j.1 then f j else 1) =
    f 0 * ∏ j : Fin n, if Even j.1 then f j.succ.succ else 1 := by sorry
