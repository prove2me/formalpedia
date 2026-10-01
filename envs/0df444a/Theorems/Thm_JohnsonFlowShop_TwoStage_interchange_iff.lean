-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_interchange_iff
-- name    : JohnsonFlowShop.TwoStage.interchange_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:40:02.011058+00:00
-- url     : https://prove2.me/theorems/df00d6a9-91b9-495a-8096-7e6c20111da5
-- title:
--   p. 63 — interchanging two adjacent items: $K'_u = K_u$ elsewhere, and (I) ⟺ (II)
-- statement:
--   Let $A, B$ be real processing times of $n$ items and $\sigma$ an order, $\sigma(k)$ being the item in position $k$. Fix a position $j$ with $j + 1 \le n - 1$, and let $\sigma'$ be the order obtained from $\sigma$ by interchanging the items in positions $j$ and $j+1$. Write $K_u$ and $K'_u$ for Johnson's quantities of $\sigma$ and $\sigma'$. Then
--
--   1. $K'_u = K_u$ for every position $u \notin \{j, j+1\}$;
--   2. relation (I) holds exactly when relation (II) holds for the items in positions $j$ and $j+1$:
--   $$
--   \max(K_j, K_{j+1}) < \max(K'_j, K'_{j+1}) \iff \min\bigl(A_{\sigma(j)}, B_{\sigma(j+1)}\bigr) < \min\bigl(A_{\sigma(j+1)}, B_{\sigma(j)}\bigr).
--   $$
--
--   So only the two affected terms of $F = \max_u K_u$ change, and comparing them reduces to comparing four processing times. This is the "Solution of problem" on p. 63 and the reduction of (I) to (II) in Theorem 1.
--
--   **Formalization Note** $\sigma' = \sigma \circ (j\ j{+}1)$ swaps positions, not item labels. $K'$ is $K$ of the interchanged order, with the upper limit $u-1$ on the $B$-sum as in the definition of $K_u$ on p. 62; the page's display of $K'_u$ prints the upper limit $u$ on the $B'$-sum, which is a typo (with it, the subtraction on p. 63 does not produce (II)). No positivity is needed.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 63, Two-stage production schedule, "Solution of problem" and Theorem 1, relations (I) and (II)

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_K

namespace JohnsonFlowShop.TwoStage

/-- p. 63, adjacent interchange and (I) ⟺ (II): let `σ'` be `σ` with the items in positions
`j` and `j + 1` interchanged. Then `K'_u = K_u` for every other position `u`, and
`max (K_j, K_{j+1}) < max (K'_j, K'_{j+1})` holds exactly when
`min (A (σ j), B (σ (j+1))) < min (A (σ (j+1)), B (σ j))`. -/
theorem interchange_iff {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j + 1 < n) :
    (∀ u : Fin n, u ≠ ⟨j, by omega⟩ → u ≠ ⟨j + 1, hj⟩ →
        Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) u = Shared.K A B σ u) ∧
    (max (Shared.K A B σ ⟨j, by omega⟩) (Shared.K A B σ ⟨j + 1, hj⟩) <
        max (Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) ⟨j, by omega⟩)
            (Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) ⟨j + 1, hj⟩) ↔
      min (A (σ ⟨j, by omega⟩)) (B (σ ⟨j + 1, hj⟩)) <
        min (A (σ ⟨j + 1, hj⟩)) (B (σ ⟨j, by omega⟩))) := by sorry

end JohnsonFlowShop.TwoStage
