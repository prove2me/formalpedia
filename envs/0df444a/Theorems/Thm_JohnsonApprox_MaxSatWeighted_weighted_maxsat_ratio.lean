-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_weighted_maxsat_ratio
-- name    : JohnsonApprox.MaxSatWeighted.weighted_maxsat_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:40:41.894284+00:00
-- url     : https://prove2.me/theorems/1ff87ed4-6f78-4975-87d1-edcfc4ffa82f
-- title:
--   Theorem 3 — R[B2, MS(k)] ≤ 2^k/(2^k − 1), attained for every k ≥ 2
-- statement:
--   Johnson's Theorem 3 reads: "For $k \geq 1$ and $n > 0$, $R[B2, \mathrm{MS}(k)](n) \le 2^k/(2^k - 1)$, with equality for all sufficiently large $n$." Here algorithm B2 is the weighted literal-selection algorithm for MAXIMUM SATISFIABILITY, $S^*$ is the largest number of clauses of $S$ satisfiable by one truth assignment, and the performance ratio of B2 on $S$ is $S^*/|\mathrm{SUB}|$ for the worst output SUB the algorithm may return. The statement formalized here is:
--
--   1. For every $k \ge 1$, every input $S$ of MS(k) (every clause has at least $k$ distinct literals) and every set SUB choosable by B2 on $S$,
--   $$(2^k - 1)\, S^* \;\le\; 2^k\, |\mathrm{SUB}|, \qquad\text{i.e.}\qquad \frac{S^*}{|\mathrm{SUB}|} \le \frac{2^k}{2^k-1}.$$
--   2. For every $k \ge 2$ there are an input $S$ of MS(k) and a set SUB choosable by B2 on $S$ with $|\mathrm{SUB}| > 0$ and
--   $$(2^k - 1)\, S^* \;=\; 2^k\, |\mathrm{SUB}|.$$
--
--   Part 1 is the classical guarantee that B2 satisfies at least a $1 - 2^{-k}$ fraction of the optimum; at $k = 1$ it says B2 satisfies at least half of the optimum. Part 2 says the constant cannot be improved.
--
--   **Formalization Note** The paper's $R[A,P](n)$ is a maximum over inputs of size at most $n$ in an unspecified encoding. Since it is a maximum over finitely many inputs and nondecreasing in $n$, "$R(n) \le c$ for all $n > 0$" is equivalent to part 1 for every input, and "equality for all sufficiently large $n$" is equivalent (given part 1) to the existence of one input attaining the ratio $c$ exactly, which is part 2. Ratios are multiplied out, so no division by zero can occur. **Correction:** the printed equality clause includes $k = 1$, where it is false: ratio 2 would force $S^* = |S|$ and every clause to be a unit clause, but on a jointly satisfiable set of unit clauses B2 never kills a clause. Equality is therefore stated for $k \ge 2$ only; the separate item `ratio_not_attained_k1` records the $k = 1$ case.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 263, Theorem 3 (proof pp. 263–264)

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Theorem 3 (p. 263), size-free and with the equality range corrected to `k ≥ 2`:
(1) for `k ≥ 1`, every output of B2 on an input of `MS(k)` satisfies
`S*/|SUB| ≤ 2^k/(2^k − 1)` (multiplied out); (2) for every `k ≥ 2` some input of `MS(k)` and
some choosable output attain the ratio `2^k/(2^k − 1)` exactly. At `k = 1` the ratio `2` is
never attained, so the printed "with equality" fails there. -/
theorem weighted_maxsat_ratio :
    (∀ k : ℕ, 1 ≤ k → ∀ S : Finset Shared.Clause, Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
      (2 ^ k - 1) * Shared.opt S ≤ 2 ^ k * X.card) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ S : Finset Shared.Clause, Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
      0 < X.card ∧ (2 ^ k - 1) * Shared.opt S = 2 ^ k * X.card) := by sorry

end JohnsonApprox.MaxSatWeighted
