-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_prod_pairs_even
-- name    : GlobalTheory.FunObj.prod_pairs_even
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:41.539158+00:00
-- url     : https://prove2.me/theorems/e7127afc-31e8-4224-ae86-a8272cb29d1d
-- title:
--   Fun Obj: prod pairs even
-- statement:
--   The Fun Obj construction uses the prod pairs even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L177-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L177-L192

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

theorem GlobalTheory.FunObj.prod_pairs_even {m : ℕ} (hm : 2 ≤ m) (he : Even m) (a b : Fin (m - 1) → ℂ) :
    (∏ j, a j) * (∏ j : Fin (m - 1), if Even (m - 2 - j) then b j else 1) =
      (∏ j : Fin (m - 2), if Even j.1 then a ⟨j, by omega⟩ * a ⟨j + 1, by omega⟩ * b ⟨j, by omega⟩ else 1) *
      (a ⟨m - 2, by omega⟩ * b ⟨m - 2, by omega⟩) := by sorry
