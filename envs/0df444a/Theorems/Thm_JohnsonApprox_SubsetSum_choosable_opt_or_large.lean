-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_choosable_opt_or_large
-- name    : JohnsonApprox.SubsetSum.choosable_opt_or_large
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:18:32.85592+00:00
-- url     : https://prove2.me/theorems/3bd6a0c4-3854-413a-a314-050f2cbd3948
-- title:
--   Proof of Theorem 1: either m(T_1) = ⟨T, s, b⟩* or m(T_1) ≥ [k/(k + 1)] · b
-- statement:
--   Let $k \ge 1$, let $\langle T, s, b\rangle$ be a SUBSET-SUM input, and let $T_1$ be choosable by algorithm $A_k$. Then either the output is optimal or its measure is at least a $k/(k+1)$ fraction of the bound:
--
--   $$m(T_1) = \langle T, s, b\rangle^* \qquad\text{or}\qquad m(T_1) \ge \frac{k}{k+1}\cdot b.$$
--
--   The paper calls this "the somewhat stronger result" it actually proves for the upper bound of Theorem 1. Since every approximate solution has measure at most $b$, so that $\langle T, s, b\rangle^* \le b$, either alternative gives $m(T_1) \ge \frac{k}{k+1}\langle T, s, b\rangle^*$.
--
--   **Formalization Note** The second alternative is written multiplicatively as $k\,b \le (k+1)\,m(T_1)$, with $k$ cast to $\mathbb{Q}$. The statement holds for every choosable output, i.e. for every resolution of the ties in Steps 1 and 3.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 260, proof of Theorem 1

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem choosable_opt_or_large {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₁ : Finset α) (hT₁ : Choosable k u T₁) :
    measure u T₁ = opt u ∨ (k : ℚ) * u.b ≤ ((k : ℚ) + 1) * measure u T₁ := by sorry

end JohnsonApprox.SubsetSum
