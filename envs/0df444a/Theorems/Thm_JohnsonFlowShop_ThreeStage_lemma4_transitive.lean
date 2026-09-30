-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_lemma4_transitive
-- name    : JohnsonFlowShop.ThreeStage.lemma4_transitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:50:41.117436+00:00
-- url     : https://prove2.me/theorems/6f7fde7c-caee-4ee8-a60a-be3234a4329c
-- title:
--   Lemma 4 — relation (IV) is transitive (except when the middle item is indifferent to both)
-- statement:
--   Let $A_1, B_1, C_1, A_2, B_2, C_2, A_3, B_3, C_3$ be real numbers. If
--
--   $$
--   \min(A_1 + B_1,\ C_2 + B_2) \le \min(A_2 + B_2,\ C_1 + B_1)
--   \quad\text{and}\quad
--   \min(A_2 + B_2,\ C_3 + B_3) \le \min(A_3 + B_3,\ C_2 + B_2),
--   $$
--
--   then
--
--   $$
--   \min(A_1 + B_1,\ C_3 + B_3) \le \min(A_3 + B_3,\ C_1 + B_1),
--   $$
--
--   unless both hypotheses hold with equality (item 2 is indifferent to both item 1 and item 3).
--
--   This is Lemma 2 (p. 64) for the times $A_i + B_i$ and $B_i + C_i$; it is what allows the definite preferences of (IV) to be arranged into one ordering by successive interchanges.
--
--   **Formalization Note** The page says only "Relation (IV) is transitive. Proof is the same as for Lemma 2", and Lemma 2 carries the exception for an item indifferent to both others. Without the exception the statement is false: take $B \equiv 0$ and $(A_i, C_i) = (5, 2), (1, 1), (2, 5)$. No positivity is assumed.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 67, Lemma 4 (with the exception of Lemma 2, p. 64)

import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- Lemma 4 (p. 67): relation (IV) is transitive, with the same exception as Lemma 2 (item 2
indifferent to both items 1 and 3). For real numbers (no positivity needed): if
`min (A₁ + B₁) (C₂ + B₂) ≤ min (A₂ + B₂) (C₁ + B₁)` and
`min (A₂ + B₂) (C₃ + B₃) ≤ min (A₃ + B₃) (C₂ + B₂)`, then
`min (A₁ + B₁) (C₃ + B₃) ≤ min (A₃ + B₃) (C₁ + B₁)`, or both hypotheses hold with equality. -/
theorem lemma4_transitive (A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : ℝ)
    (h₁₂ : min (A₁ + B₁) (C₂ + B₂) ≤ min (A₂ + B₂) (C₁ + B₁))
    (h₂₃ : min (A₂ + B₂) (C₃ + B₃) ≤ min (A₃ + B₃) (C₂ + B₂)) :
    min (A₁ + B₁) (C₃ + B₃) ≤ min (A₃ + B₃) (C₁ + B₁) ∨
      (min (A₁ + B₁) (C₂ + B₂) = min (A₂ + B₂) (C₁ + B₁) ∧
        min (A₂ + B₂) (C₃ + B₃) = min (A₃ + B₃) (C₂ + B₂)) := by sorry

end JohnsonFlowShop.ThreeStage
