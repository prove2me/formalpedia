-- Prove2me | Theorems.Thm_OnlinePrimalDual_Framework_algorithm3_competitive_ratio_v2
-- name    : OnlinePrimalDual.Framework.algorithm3_competitive_ratio_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:04.856359+00:00
-- url     : https://prove2.me/theorems/62edb1d1-c169-4147-8143-2495298f4aad
-- title:
--   Theorem 4.3 — Algorithm 3 (complementary slackness): $2(1+\ln d)$-competitive covering, $2$-competitive packing with violation $\le 1+\ln d$
-- statement:
--   In the online packing–covering framework of Section 4.1 (covering LP $\min\sum_i c_i x_i$, $\sum_{i\in S(j)} x_i \ge 1$, $x\ge0$; packing dual $\max\sum_j y_j$, $\sum_{j: i\in S(j)} y_j \le c_i$, $y \ge 0$; $|S(j)| \le d$; constraints arriving in the order `ord`, a permutation of $J$; every $S(j)$ non-empty), let $y$ be the final dual vector of Algorithm 3 (`raiseRun inst (alg3X inst) ord`): starting from $y=0$, when constraint $j$ arrives, $y_j$ is increased continuously while $\sum_{i\in S(j)} x_i < 1$, where throughout $x_i = 0$ while $\sigma_i := \sum_{j: i\in S(j)} y_j < c_i$, $x_i$ jumps to $1/d$ when $\sigma_i$ reaches $c_i$ (step (1b)), and then $x_i = \min\{1, \tfrac1d \exp(\sigma_i/c_i - 1)\}$ (step (1c), frozen at $1$) — the closed form `alg3X`; let $x = \texttt{alg3X}(y)$ be the final primal vector. Then
--
--   1. $x$ is a feasible covering solution;
--   2. $y \ge 0$ and $y$ violates each packing constraint by a factor of at most $1+\ln d$: $\sum_{j: i\in S(j)} y_j \le c_i(1+\ln d)$ for every $i$;
--   3. $x$ is $2(1+\ln d)$-competitive: $\sum_i c_i x_i \le 2(1+\ln d)\sum_i c_i x''_i$ for every feasible covering solution $x''$;
--   4. $y$ is $2$-competitive: $\sum_j y''_j \le 2\sum_j y_j$ for every feasible packing solution $y''$.
--
--   **Formalization Note.** The retired version took $y$ as a free non-negative vector constrained only by final covering feasibility, so a huge $y$ (e.g. $y=100$ on a one-variable instance) saturated every $x_i$ at $1$, kept the hypotheses and violated the packing bound by an unbounded factor. The new statement computes $y$ by a definition (`raiseRun`) that raises each arriving dual variable exactly until its constraint is covered — the infimum of the admissible stopping values, attained because `alg3X` is non-decreasing and right-continuous in $y_j$ and reaches $1$ — so the theorem is about Algorithm 3's own output; Claim (1) is a conclusion rather than a hypothesis. Conventions made explicit: $S(j)\ne\emptyset$ for all $j$ (feasibility of the covering LP, the section's standing convention; it excludes the junk value $\inf\emptyset=0$ and gives $d\ge1$, so $\ln d \ge 0$); the arrival order is a permutation of $J$; competitiveness is stated by weak duality against every feasible offline solution of the opposite LP, with the constants $1+\ln d$, $2(1+\ln d)$ and $2$ of the book's proof (Claims (2)-(3), p. 125-126). Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 124-126, Theorem 4.3 (Algorithm 3)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg3X
import Definitions.Def_OnlinePrimalDual_Framework_raiseRun_v2

namespace OnlinePrimalDual.Framework

/-- **Theorem 4.3** (Buchbinder & Naor, FnT TCS 2009, p. 124-126), Algorithm 3, the
complementary-slackness algorithm — the goal of this mission. `ord` is the online arrival order
of the covering constraints (a permutation of `J`); `y = raiseRun inst (alg3X inst) ord` is
Algorithm 3's own final dual vector (p. 124: each arriving `yⱼ` is increased continuously
*exactly while* `∑_{i ∈ S(j)} xᵢ < 1`, with `x` given by the closed form `alg3X` of steps
(1b)-(1c)), and `x = alg3X inst y` its final primal vector — both computed from the instance and
the arrival order alone. The retired version took `y` as a free vector pinned only by final
covering feasibility, which admits inflated `y`. `hS` is the standing feasibility assumption of
the covering LP (every constraint involves at least one variable). Conclusions, with the exact
constants the book's proof derives: the covering solution is feasible (Claim (1), p. 125); the
packing solution `y` is non-negative and violates each packing constraint by a factor of at most
`1 + ln d` (Claim (2), p. 125, "∑ yⱼ ≤ cᵢ(1 + ln d)"); the covering solution is
`2(1 + ln d)`-competitive against every feasible offline covering solution (Claim (3), `P ≤ 2D`,
p. 125-126, with the rescaled `y` and weak duality); the packing solution is `2`-competitive
against every feasible offline packing solution (`P ≤ 2D` and weak duality both ways). -/
theorem algorithm3_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg3X inst) ord
    let x : I → ℝ := alg3X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i * (1 + Real.log inst.d)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * (1 + Real.log inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework
