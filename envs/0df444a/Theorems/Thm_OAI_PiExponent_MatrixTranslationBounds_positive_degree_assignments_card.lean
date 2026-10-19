-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_positive_degree_assignments_card
-- name    : OAI.PiExponent.MatrixTranslationBounds.positive_degree_assignments_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:34:39.887264+00:00
-- url     : https://prove2.me/theorems/d461a3b5-c37e-46dd-afcf-c4f7054956d0
-- title:
--   Count positive degree assignments
-- statement:
--   The number of functions into `Fin (k + 1)` with every value positive and sum `k` is at most `Nat.choose k (Fintype.card ι)`, including the empty-index and impossible-degree cases.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.MatrixTranslationBounds.positive_degree_assignments_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ)
    [DecidablePred (fun f : ι → Fin (k + 1) => (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k)] :
    Fintype.card {f : ι → Fin (k + 1) //
      (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k} ≤
      Nat.choose k (Fintype.card ι) := by sorry
