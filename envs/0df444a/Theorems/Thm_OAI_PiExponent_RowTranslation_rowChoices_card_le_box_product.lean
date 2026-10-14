-- Prove2me | Theorems.Thm_OAI_PiExponent_RowTranslation_rowChoices_card_le_box_product
-- name    : OAI.PiExponent.RowTranslation.rowChoices_card_le_box_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T09:52:50.370271+00:00
-- url     : https://prove2.me/theorems/3ebc8875-af58-4ff0-a21c-455f2222fda7
-- title:
--   Cardinality bound for boxed row-choice fibers
-- statement:
--   For a finite index set whose multi-indices lie in a coordinate box of side length N, the number of dependent row choices is at most the number of indices times the box size for the fiber coordinates times the final Fin factor.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L35-L47

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

theorem OAI.PiExponent.RowTranslation.rowChoices_card_le_box_product
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s N : ℕ)
    (hbox : ∀ a ∈ S, ∀ i, a i < N) :
    Fintype.card (RowChoices S β s) ≤
      Fintype.card S * N ^ Fintype.card σ * (s + 1) := by
  sorry
