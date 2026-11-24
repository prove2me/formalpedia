-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_tensor_shift
-- name    : GlobalTheory.FunObj.FiniteSupport.tensor_shift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:46.476827+00:00
-- url     : https://prove2.me/theorems/7306186b-5f05-4e24-bf3b-dea6f03ac946
-- title:
--   Finite Support: tensor shift
-- statement:
--   The Finite Support construction uses the tensor shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L265-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L265-L286

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
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.FunObj.FiniteSupport.tensor_shift {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G) (v : Vars G) {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d)
    (hb : ∀ (j : ℕ) (h : j < G.m - 1), Bd (valuation k ((ϖ ^ e : kˣ) : k)) (((g (G.m, j + 1))⁻¹).val *
      (d ⟨j, h⟩).reindex (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; dsimp only; omega)) * (g (G.m, j)).val)) :
    T (G.moveArgs .one g (fill hs x y (shiftVars d + v))) = T (G.moveArgs .one g (fill hs x y v)) := by sorry
