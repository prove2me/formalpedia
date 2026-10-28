-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_thm_4_3_shortening_count
-- name    : NonconvexCost.Complexity.thm_4_3_shortening_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:50.091919+00:00
-- url     : https://prove2.me/theorems/58fc741d-839e-47ed-941a-a0424ea7a646
-- title:
--   Proof of Theorem 4.3, p. 10 — after k shortening steps with |g_k| > ε, k < 16(L²/ε² − 1)
-- statement:
--   Let $L,\epsilon>0$ and let $(g_i)_{i\ge0}$, $(g'_i)_{i\ge0}$ be sequences in $X$ with $|g_0|\le L$ and, for every $i$,
--   $$|g'_i|\le L,\qquad \langle g'_i,g_i\rangle<\tfrac12|g_i|^2,\qquad g_{i+1}\ \text{a shortest vector in } [g_i,g'_i].$$
--   If after $k$ such shortening steps the subgradient is still inadequate, $|g_k|>\epsilon$, then
--   $$k<16\Big(\frac{L^2}{\epsilon^2}-1\Big).$$
--
--   Hence, starting from any point with an inadequate subgradient, no more than $16L^2/\epsilon^2$ line searches are needed before an adequate subgradient is found.
--
--   **Formalization Note** The statement is purely about the sequence of shortening steps; the inequality $\langle g'_i,g_i\rangle<\frac12|g_i|^2$ is what each successful line search provides.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, pp. 9–10, proof of Theorem 4.3

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

namespace NonconvexCost.Complexity

open scoped RealInnerProductSpace

theorem thm_4_3_shortening_count {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε) (g g' : ℕ → X) (hg0 : ‖g 0‖ ≤ L)
    (hg' : ∀ i, ‖g' i‖ ≤ L) (hinner : ∀ i, ⟪g' i, g i⟫ < ‖g i‖ ^ 2 / 2)
    (hshort : ∀ i, IsShortestIn (g i) (g' i) (g (i + 1))) (k : ℕ) (hk : ε < ‖g k‖) :
    (k : ℝ) < 16 * (L ^ 2 / ε ^ 2 - 1) := by sorry

end NonconvexCost.Complexity
