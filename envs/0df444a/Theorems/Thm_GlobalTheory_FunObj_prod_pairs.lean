-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_prod_pairs
-- name    : GlobalTheory.FunObj.prod_pairs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:28.208676+00:00
-- url     : https://prove2.me/theorems/293ab627-5dad-4c93-a996-d11ec8f3e749
-- title:
--   Fun Obj: prod pairs
-- statement:
--   The Fun Obj construction uses the prod pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L155-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L155-L164

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

theorem GlobalTheory.FunObj.prod_pairs (q : ℕ) (a : Fin (2 * q + 1) → ℂ) :
    ∏ j : Fin (2 * q + 1), a j = (∏ j : Fin (2 * q), if Even j.1 then a ⟨j, by omega⟩ * a ⟨j + 1, by omega⟩ else 1) *
      a ⟨2 * q, by omega⟩ := by sorry
