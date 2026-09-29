-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_overlapGreedy_exactCover_ratio
-- name    : JohnsonApprox.ExactCover.overlapGreedy_exactCover_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:35:03.402797+00:00
-- url     : https://prove2.me/theorems/4f146e2c-0729-4a02-b473-9b5b73132804
-- title:
--   Theorem 6 — R[C2, EC(k)](n) ≤ 1 + ln(k) ≤ Σ_{j=1}^k (1/j) + 1/2, and R[C2, EC(k)](n) ≥ Σ_{j=1}^k (1/j) for large n
-- statement:
--   **Theorem 6** (Johnson 1974). For all $k \ge 1$ and $n > 0$,
--   $$R[C2, EC(k)](n) \le 1 + \ln(k) \le \sum_{j=1}^{k} \frac{1}{j} + \frac{1}{2},$$
--   and for all sufficiently large $n$, $R[C2, EC(k)](n) \ge \sum_{j=1}^k (1/j)$.
--
--   Here EC$(k)$ is SET COVERING II restricted to families of sets with at most $k$ points each, measured by the total size $\sum_{S \in F'} |S|$ of a subcover $F'$, and C2 is the greedy algorithm that repeatedly adds the set minimizing $|S - \mathrm{UNCOV}|/|S \cap \mathrm{UNCOV}|$. Stated without the problem size $n$, for every $k \ge 1$:
--
--   1. for every input $F$ of EC$(k)$ with optimum $F^*$ and every subcover $M$ choosable by C2 on $F$,
--   $$m_{EC}(M) \le (1 + \ln k)\, F^*;$$
--   2. $1 + \ln k \le \sum_{j=1}^k \frac{1}{j} + \frac12$;
--   3. there are an input $F$ of EC$(k)$ with $F^* > 0$ and a subcover $M$ choosable by C2 on $F$ with
--   $$m_{EC}(M) \ge \Big(\sum_{j=1}^k \frac1j\Big) F^*.$$
--
--   The paper notes (without proof) that even an algorithm returning a minimum-cardinality subcover can be off by a factor of $k$ on this measure; C2 is within a logarithmic factor of the least-overlap cover, and its guarantee matches, up to an additive $1/2$, the guarantee $\sum_{j=1}^k 1/j$ of the greedy algorithm C1 for minimum-cardinality set cover.
--
--   **Formalization Note** The paper's $R[A, P](n)$ is the maximum, over inputs of size at most $n$, of the worst ratio $A(u)/u^*$ over outputs choosable by $A$ (p. 259); its notion of size is left unspecified. Part 1 states the bound for every input and every choosable output, which is equivalent to $R[C2, EC(k)](n) \le 1 + \ln k$ for all $n$. Part 3 exhibits one input and one choosable output attaining ratio at least $\sum_{j=1}^k 1/j$; since $R$ is a maximum over the finitely many inputs of size at most $n$ and is nondecreasing in $n$, this is equivalent to the claim for all sufficiently large $n$. Ratios are stated multiplicatively (no division by $F^*$; for $F^* = 0$ part 1 reads $0 \le 0$). Choosability is the nondeterministic run relation of `C2`, with all ties at Step 3 allowed. The input in part 3 has points in $\mathbb N \times \mathbb N$; $\sum_{j=1}^k 1/j$ is Mathlib's `harmonic k`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, Theorem 6

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Theorem 6 (p. 271), size-free: for all `k ≥ 1`, (1) every subcover choosable by C2 on an
input of `EC(k)` has measure at most `(1 + ln k) · F*`; (2) `1 + ln k ≤ Σ_{j=1}^k 1/j + 1/2`;
(3) some input of `EC(k)` with `F* > 0` has a choosable subcover of measure at least
`(Σ_{j=1}^k 1/j) · F*`. -/
theorem overlapGreedy_exactCover_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (α : Type) [DecidableEq α] (F : Input α), InEC k F →
      ∀ M, Choosable F M → (F.measure M : ℝ) ≤ (1 + Real.log k) * (F.opt : ℝ)) ∧
    1 + Real.log k ≤ (harmonic k : ℝ) + 1 / 2 ∧
    (∃ F : Input (ℕ × ℕ), InEC k F ∧ 0 < F.opt ∧
      ∃ M, Choosable F M ∧ (harmonic k : ℝ) * (F.opt : ℝ) ≤ (F.measure M : ℝ)) := by sorry

end JohnsonApprox.ExactCover
