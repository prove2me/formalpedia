-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_interchange_F_le
-- name    : JohnsonFlowShop.TwoStage.interchange_F_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:40:43.123862+00:00
-- url     : https://prove2.me/theorems/4abab7ed-3f86-4655-8017-144c71daa7ed
-- title:
--   p. 63, proof of Theorem 1 — an interchange according to (II) gives a value of F smaller than or the same as before
-- statement:
--   Let $n \ge 1$, let $A, B$ be real processing times, and let $\sigma$ be an order, $\sigma(k)$ being the item in position $k$. Fix a position $j$ with $j + 1 \le n-1$, and let $\sigma'$ be $\sigma$ with the items in positions $j$ and $j+1$ interchanged. If the items in positions $j, j+1$ of $\sigma$ are in an order allowed by relation (II),
--   $$
--   \min\bigl(A_{\sigma(j)}, B_{\sigma(j+1)}\bigr) \le \min\bigl(A_{\sigma(j+1)}, B_{\sigma(j)}\bigr),
--   $$
--   then
--   $$
--   F(\sigma) \le F(\sigma').
--   $$
--   Read from $\sigma'$ to $\sigma$: interchanging two consecutive items into the order that (II) allows gives a value of $F = \max_u K_u$ smaller than or the same as before. This is the step by which Johnson passes from an arbitrary sequence $S_0$ to $S^*$.
--
--   **Formalization Note** $\sigma' = \sigma \circ (j\ j{+}1)$ swaps positions; $F$ requires $n \ge 1$ (`[NeZero n]`). No positivity is needed.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 63, Theorem 1 ("each interchange will give a value of F smaller than or the same as before")

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_K
import Definitions.Def_JohnsonFlowShop_TwoStage_F

namespace JohnsonFlowShop.TwoStage

/-- p. 63 (proof of Theorem 1): if the items in positions `j` and `j + 1` of `σ` are in an order
allowed by (II), `min (A (σ j), B (σ (j+1))) ≤ min (A (σ (j+1)), B (σ j))`, then interchanging
them does not decrease `F`: `F(σ) ≤ F(σ')`. Equivalently, interchanging an adjacent pair into
the order (II) prefers gives a value of `F` smaller than or the same as before. -/
theorem interchange_F_le {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j + 1 < n)
    (hII : min (A (σ ⟨j, by omega⟩)) (B (σ ⟨j + 1, hj⟩)) ≤
      min (A (σ ⟨j + 1, hj⟩)) (B (σ ⟨j, by omega⟩))) :
    F A B σ ≤ F A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) := by sorry

end JohnsonFlowShop.TwoStage
