-- Prove2me | Theorems.Thm_OnlinePrimalDual_Framework_algorithm1_competitive_ratio_v2
-- name    : OnlinePrimalDual.Framework.algorithm1_competitive_ratio_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:45.465649+00:00
-- url     : https://prove2.me/theorems/dbc27865-4c96-4f7c-a7c9-1d3808d63886
-- title:
--   Theorem 4.1 — Algorithm 1 (basic discrete algorithm): $2\log_2(3d+1)$-competitive covering solution, $2$-competitive integral packing solution with violation $\le \log_2(3d+1)$
-- statement:
--   Consider the online packing–covering framework of Section 4.1: a covering LP $\min\sum_i c_i x_i$ subject to $\sum_{i\in S(j)} x_i \ge 1$ for every constraint $j$ and $x\ge 0$, whose constraints arrive online in the order `ord` (a permutation of $J$), and its packing dual $\max\sum_j y_j$ subject to $\sum_{j: i\in S(j)} y_j \le c_i$, $y \ge 0$. Assume $c_i \ge 1$ for all $i$, every constraint involves at least one variable ($S(j)\neq\emptyset$), and $|S(j)| \le d$. Let $(x, y)$ be the output of Algorithm 1 (`alg1Run inst ord`): starting from $x = 0$, $y = 0$, each arriving constraint $j$ is processed by the inner loop "while $\sum_{i\in S(j)} x_i < 1$: for each $i \in S(j)$, $x_i \leftarrow x_i(1+1/c_i) + 1/(|S(j)|\,c_i)$; $y_j \leftarrow y_j + 1$". Then
--
--   1. the covering solution $x$ is feasible: $\sum_{i\in S(j)} x_i \ge 1$ for every $j$;
--   2. the integral packing solution $y$ violates each packing constraint by a factor of at most $\log_2(3d+1)$: $\sum_{j: i\in S(j)} y_j \le c_i \log_2(3d+1)$ for every $i$;
--   3. $x$ is $2\log_2(3d+1)$-competitive: $\sum_i c_i x_i \le 2\log_2(3d+1)\sum_i c_i x''_i$ for every feasible covering solution $x''$;
--   4. $y$ is $2$-competitive: $\sum_j y''_j \le 2\sum_j y_j$ for every feasible packing solution $y''$.
--
--   **Formalization Note.** The retired version took the iteration counts $t_j$ as a free variable constrained only by final primal feasibility, which is monotone in $t$, so over-incremented runs (e.g. $t = 3$ on a one-variable instance, violating bound 2) were admitted. The new statement computes $x$ and $y$ by a definition (`alg1Run`) that executes Algorithm 1 literally — each constraint's inner loop runs exactly while the constraint is violated — so the theorem is about the algorithm's own output; feasibility of $x$ (the book's Claim (1)) is stated as a conclusion rather than assumed. Conventions made explicit: $c_i \ge 1$ (the book's standing assumption for Algorithm 1, p. 118); $S(j) \neq \emptyset$ for all $j$ (feasibility of the covering LP, the section's standing convention — otherwise the book's loop does not terminate; it also forces $d \ge 1$); the arrival order is a permutation of $J$; competitiveness is stated by weak duality against every feasible offline solution of the opposite LP, as in the retired version, with the constants $\log_2(3d+1)$ and $2$ transcribed from the captain's reading of the proof on p. 120. Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 118-120, Theorem 4.1 (Algorithm 1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg1Run_v2

namespace OnlinePrimalDual.Framework

/-- **Theorem 4.1** (Buchbinder & Naor, FnT TCS 2009, p. 118-120), Algorithm 1, the basic discrete
algorithm. `ord` is the online arrival order of the covering constraints (`hord_nodup`/`hord_mem`:
a permutation of `J`); `alg1Run inst ord` is Algorithm 1's own output (p. 118, steps (1a)-(1b)
applied verbatim: each arriving constraint is processed by inner-loop iterations *exactly while*
it is still violated, and `yⱼ` counts them), so `x` and `y` below are computed from the instance
and the arrival order alone — the retired version let the iteration counts be a free variable
pinned only by final feasibility, which admits over-incremented runs. `hc1` is the book's standing
assumption `cᵢ ≥ 1` for this algorithm (p. 118); `hS` is the standing feasibility assumption of the
covering LP (every constraint involves at least one variable; otherwise the book's loop never
terminates). Conclusions: the covering solution is feasible (Claim (1), part of "produces a
covering solution"); the integral packing solution `y` violates each packing constraint by a
factor of at most `log₂(3d+1)` (Claims (2)-(3) with the proof's own displayed bound, p. 120); the
covering solution is `2·log₂(3d+1)`-competitive against every feasible offline covering solution;
the packing solution is `2`-competitive against every feasible offline packing solution
(`P ≤ 2D` and weak duality both ways). -/
theorem algorithm1_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i)
    (hS : ∀ j, (inst.S j).Nonempty) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let x : I → ℝ := (alg1Run inst ord).1
    let y : J → ℝ := fun j => ((alg1Run inst ord).2 j : ℝ)
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    (∀ i : I, dualSum inst y i ≤ inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework
