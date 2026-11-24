-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_exists_rowR_mul
-- name    : GlobalTheory.FunObj.FiniteSupport.exists_rowR_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:47.574496+00:00
-- url     : https://prove2.me/theorems/ad14d913-1a76-4636-936f-8f59b4176ecd
-- title:
--   Finite Support: exists row R mul
-- statement:
--   The Finite Support construction uses the exists row R mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L288-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L288-L343

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

theorem GlobalTheory.FunObj.FiniteSupport.exists_rowR_mul (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (s : kˣ) : ∃ δ : ValueGroupWithZero k, ∀ (keep : Bool) (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G)
      (j : ℕ) (hj : j < G.m - 2), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      Bd (valuation k (s : k)) (g (G.m, j)).val → Bd (valuation k (s : k)) ((g (G.m, j))⁻¹).val →
      ∃ r ∈ rowR hs (j := j + 1) (by omega), ∃ w : GL (Fin (G.rank (G.m, j + 1))) k,
        Bd δ w.val ∧ Bd δ (w⁻¹).val ∧ g (G.m, j + 1) = r * w := by sorry
