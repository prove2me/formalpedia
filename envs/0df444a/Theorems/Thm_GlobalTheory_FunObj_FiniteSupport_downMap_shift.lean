-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_downMap_shift
-- name    : GlobalTheory.FunObj.FiniteSupport.downMap_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:05.364851+00:00
-- url     : https://prove2.me/theorems/a3ae774a-5cdf-4158-8d2c-1ee9269e6803
-- title:
--   Finite Support: down Map shift
-- statement:
--   The Finite Support construction uses the down Map shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L193-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L193-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)

theorem GlobalTheory.FunObj.FiniteSupport.downMap_shift {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) (j : ℕ) :
    downMap hs x (shiftVars d + e) j - downMap hs x e j = if h : j < G.m - 1 then
      (d ⟨j, h⟩).reindex (frame (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (by have := topRank_add hs j; dsimp only; omega)) else 0 := by sorry
