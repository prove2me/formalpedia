-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_excluded_small_does_not_fit
-- name    : JohnsonApprox.SubsetSum.excluded_small_does_not_fit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:18:12.08041+00:00
-- url     : https://prove2.me/theorems/3073f3ce-7569-449e-9229-de006c22e8ac
-- title:
--   Proof of Theorem 1: an excluded small element does not fit, so m(T_1) > kb/(k + 1)
-- statement:
--   Let $k \ge 1$, let $\langle T, s, b\rangle$ be a SUBSET-SUM input, and let $T_1$ be choosable by algorithm $A_k$. Suppose some element $x \in T$ with $x \notin T_1$ is small, i.e. $s(x) \le b/(k+1)$. Then
--
--   1. $s(x) + m(T_1) > b$ (Step 2 of $A_k$ halted with $x$ still in LEFT);
--   2. $m(T_1) > \dfrac{k\,b}{k+1}$;
--   3. $m(T_1) \ge \dfrac{k}{k+1}\,\langle T, s, b\rangle^*$.
--
--   This is the paper's chain
--
--   $$m(T_1) > b - s(x) \ge b - \frac{b}{k+1} = \frac{kb}{k+1} \ge \frac{k}{k+1}\,\langle T, s, b\rangle^*.$$
--
--   It is the second half of the case analysis behind the upper bound of Theorem 1: if the algorithm leaves out any small element, its output already has measure within a factor $k/(k+1)$ of $b$.
--
--   **Formalization Note** The three conclusions are stated multiplicatively, without division: $b < s(x) + m(T_1)$, $k\,b < (k+1)\,m(T_1)$ and $k\,\langle T,s,b\rangle^* \le (k+1)\,m(T_1)$, with $k$ cast to $\mathbb{Q}$. The element $x$ is any element of $T$ outside $T_1$ (in the paper it comes from an optimal solution $T_0$, which is a special case).
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 261, proof of Theorem 1

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem excluded_small_does_not_fit {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (u : Input α) (T₁ : Finset α) (hT₁ : Choosable k u T₁) (x : α) (hxT : x ∈ u.T)
    (hxT₁ : x ∉ T₁) (hsmall : u.s x ≤ u.b / ((k : ℚ) + 1)) :
    u.b < u.s x + measure u T₁ ∧
      (k : ℚ) * u.b < ((k : ℚ) + 1) * measure u T₁ ∧
      (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁ := by sorry

end JohnsonApprox.SubsetSum
