-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_char_eq_one
-- name    : GlobalTheory.FunObj.FiniteSupport.char_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:00.35421+00:00
-- url     : https://prove2.me/theorems/e4ede3fa-ae96-4ec5-9551-09078b4eecab
-- title:
--   Finite Support: char eq one
-- statement:
--   The Finite Support construction uses the char eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L247-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L247-L261

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem GlobalTheory.FunObj.FiniteSupport.char_eq_one {S : G.Args → ℂ} {x : ColArgs G} {y : RowArgs G} (hne : flatTensor hs ψ ν S x y ≠ 0)
    {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (hS : ∀ e, S (fill hs x y (shiftVars d + e)) = S (fill hs x y e)) :
    ψ (∑ j, ch (d j)) = 1 := by sorry
