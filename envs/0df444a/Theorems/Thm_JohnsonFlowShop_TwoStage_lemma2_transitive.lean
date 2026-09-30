-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_lemma2_transitive
-- name    : JohnsonFlowShop.TwoStage.lemma2_transitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:41:08.28405+00:00
-- url     : https://prove2.me/theorems/b481787b-3013-4f02-a2ce-87566975a3bc
-- title:
--   Lemma 2 — relation (II) is transitive except when item 2 is indifferent to both 1 and 3
-- statement:
--   Let $A_1, B_1, A_2, B_2, A_3, B_3$ be real numbers (the processing times of three items on the two machines). Suppose
--   $$
--   \min(A_1, B_2) \le \min(A_2, B_1) \quad\text{and}\quad \min(A_2, B_3) \le \min(A_3, B_2).
--   $$
--   Then
--   $$
--   \min(A_1, B_3) \le \min(A_3, B_1),
--   $$
--   or else item 2 is indifferent to both items 1 and 3, that is, $\min(A_1, B_2) = \min(A_2, B_1)$ and $\min(A_2, B_3) = \min(A_3, B_2)$.
--
--   This is Johnson's Lemma 2, "Relation (II) is transitive", with its stated exception. It is what makes an order consistent with all definite preferences exist. The exception is needed: $(A_i, B_i) = (5,2), (1,1), (2,5)$ satisfies both hypotheses, but $\min(5,5) \le \min(2,2)$ fails.
--
--   **Formalization Note** The statement is pure min-algebra and needs no positivity.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 64, Lemma 2

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- Lemma 2 (p. 64): relation (II) is transitive, except possibly when item 2 is indifferent to
both items 1 and 3. For real numbers (no positivity needed): if
`min A₁ B₂ ≤ min A₂ B₁` and `min A₂ B₃ ≤ min A₃ B₂`, then `min A₁ B₃ ≤ min A₃ B₁`, or
`min A₁ B₂ = min A₂ B₁` and `min A₂ B₃ = min A₃ B₂`. -/
theorem lemma2_transitive (A₁ B₁ A₂ B₂ A₃ B₃ : ℝ)
    (h₁₂ : min A₁ B₂ ≤ min A₂ B₁) (h₂₃ : min A₂ B₃ ≤ min A₃ B₂) :
    min A₁ B₃ ≤ min A₃ B₁ ∨ (min A₁ B₂ = min A₂ B₁ ∧ min A₂ B₃ = min A₃ B₂) := by sorry

end JohnsonFlowShop.TwoStage
