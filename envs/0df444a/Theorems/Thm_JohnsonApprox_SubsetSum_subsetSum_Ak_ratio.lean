-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_subsetSum_Ak_ratio
-- name    : JohnsonApprox.SubsetSum.subsetSum_Ak_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:19:46.783598+00:00
-- url     : https://prove2.me/theorems/3f3151d5-fa65-4417-b45d-23d7abe91a7f
-- title:
--   Theorem 1 — R[A_k](n) ≤ (k + 1)/k and lim_{n→∞} R[A_k](n) = (k + 1)/k
-- statement:
--   This is Theorem 1 of Johnson (1974) for the SUBSET-SUM algorithms $A_k$. The paper states:
--
--   > THEOREM 1. For k ≥ 1 and n > 0, R[A_k](n) ≤ (k + 1)/k, lim_{n→∞} R[A_k](n) = (k + 1)/k.
--
--   Here, for a maximization problem, the performance ratio of an algorithm $A$ on input $u$ is $r(A, u) = u^*/A(u)$, where $u^*$ is the optimal measure and $A(u)$ is the smallest measure of an output choosable by $A$ on $u$; $R[A](n)$ is the maximum of $r(A,u)$ over inputs of size at most $n$.
--
--   Fix $k \ge 1$. The theorem is formalized as the following two statements.
--
--   1. **Upper bound.** For every SUBSET-SUM input $\langle T, s, b\rangle$ and every set $T_1$ choosable by $A_k$ on it,
--      $$k\,\langle T, s, b\rangle^* \le (k+1)\, m(T_1).$$
--   2. **Limit.** For every rational $\delta > 0$ there are an input $\langle T, s, b\rangle$ and a set $T_1$ choosable by $A_k$ on it with $m(T_1) > 0$ and
--      $$\Big(\frac{k+1}{k} - \delta\Big)\, m(T_1) < \langle T, s, b\rangle^*,$$
--      i.e. $\langle T, s, b\rangle^*/m(T_1) > (k+1)/k - \delta$.
--
--   The algorithms $A_k$ run in time polynomial in the input for each fixed $k$ and have ratio tending to $1$ as $k$ grows, so SUBSET-SUM has, for every $\epsilon > 0$, a polynomial-time algorithm with worst-case ratio at most $1 + \epsilon$.
--
--   **Formalization Note** The paper's $R[A_k](n)$ is a maximum over inputs of size at most $n$ "in some standard notation", which is never fixed; the formalization is size-free. Part 1 for all inputs is equivalent to $R[A_k](n) \le (k+1)/k$ for all $n$ (the worst choosable output is one of the choosable outputs). Given part 1, and since $R[A_k](n)$ is nondecreasing in $n$ and every input has some finite size, "$\lim_{n\to\infty} R[A_k](n) = (k+1)/k$" is equivalent to part 2: the supremum of the ratio over all inputs equals $(k+1)/k$. Part 2 exhibits one choosable output with a large ratio; the worst choosable output of the same input has a ratio at least as large, so this is the same claim as for the paper's $r(A_k, u)$. Ratios are written multiplicatively, never as a division, so an input with $m(T_1) = 0$ cannot satisfy a bound vacuously; part 2 requires $m(T_1) > 0$. The value $(k+1)/k$ is not claimed to be attained. Sizes and $b$ are rationals, as in the paper; the witness inputs of part 2 have ground sets in $\mathbb{N}$, which loses no generality since every finite set can be relabelled.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 260, Theorem 1

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem subsetSum_Ak_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (α : Type) [DecidableEq α] (u : Input α) (T₁ : Finset α), Choosable k u T₁ →
        (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁) ∧
      (∀ δ : ℚ, 0 < δ → ∃ (u : Input ℕ) (T₁ : Finset ℕ), Choosable k u T₁ ∧
        0 < measure u T₁ ∧ (((k : ℚ) + 1) / k - δ) * measure u T₁ < opt u) := by sorry

end JohnsonApprox.SubsetSum
