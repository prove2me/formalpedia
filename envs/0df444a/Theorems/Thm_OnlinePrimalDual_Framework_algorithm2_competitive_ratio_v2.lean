-- Prove2me | Theorems.Thm_OnlinePrimalDual_Framework_algorithm2_competitive_ratio_v2
-- name    : OnlinePrimalDual.Framework.algorithm2_competitive_ratio_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:46.911345+00:00
-- url     : https://prove2.me/theorems/e81771c0-52eb-4dce-bd98-40ad012fbe88
-- title:
--   Theorem 4.2 — Algorithm 2 (the continuous algorithm) produces a feasible packing solution and $2\ln(1+d)$-competitive covering and packing solutions
-- statement:
--   In the online packing–covering framework of Section 4.1 (covering LP $\min\sum_i c_i x_i$, $\sum_{i\in S(j)} x_i \ge 1$, $x \ge 0$; packing dual $\max\sum_j y_j$, $\sum_{j: i\in S(j)} y_j \le c_i$, $y\ge 0$; $|S(j)| \le d$; constraints arriving in the order `ord`, a permutation of $J$; every $S(j)$ non-empty), let $y$ be the final dual vector of Algorithm 2 (`raiseRun inst (alg2X inst) ord`): starting from $y = 0$, when constraint $j$ arrives, $y_j$ is increased continuously while $\sum_{i\in S(j)} x_i < 1$, where throughout $x_i = \frac{1}{d}\Big(\exp\big(\tfrac{\ln(1+d)}{c_i}\sum_{j: i\in S(j)} y_j\big) - 1\Big)$ (`alg2X`), and let $x = \texttt{alg2X}(y)$ be the final primal vector. Then
--
--   1. $x$ is a feasible covering solution;
--   2. $y$ is a feasible packing solution: $y \ge 0$ and $\sum_{j: i\in S(j)} y_j \le c_i$ for every $i$ (no violation);
--   3. $x$ is $2\ln(1+d)$-competitive: $\sum_i c_i x_i \le 2\ln(1+d)\sum_i c_i x''_i$ for every feasible covering solution $x''$;
--   4. $y$ is $2\ln(1+d)$-competitive: $\sum_j y''_j \le 2\ln(1+d)\sum_j y_j$ for every feasible packing solution $y''$.
--
--   **Formalization Note.** The retired version took $y$ as a free non-negative vector constrained only by final covering feasibility, so inflating $y$ past the point where its constraint is covered (e.g. $y = 2$ on a one-variable instance) kept the hypotheses and broke packing feasibility. The new statement computes $y$ by a definition (`raiseRun`) that raises each arriving dual variable exactly until its constraint is covered — the infimum of the admissible stopping values, which the monotone, continuous and unbounded rule `alg2X` attains — so the theorem is about Algorithm 2's own output; Claim (1) is a conclusion rather than a hypothesis. Conventions made explicit: $S(j)\ne\emptyset$ for all $j$ (feasibility of the covering LP, the section's standing convention; it also excludes the junk value $\inf\emptyset = 0$); the arrival order is a permutation of $J$; competitiveness is stated by weak duality against every feasible offline solution of the opposite LP; packing feasibility includes $y \ge 0$. Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 121-122, Theorem 4.2 (Algorithm 2)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg2X
import Definitions.Def_OnlinePrimalDual_Framework_raiseRun_v2

namespace OnlinePrimalDual.Framework

/-- **Theorem 4.2** (Buchbinder & Naor, FnT TCS 2009, p. 121-122), Algorithm 2, the continuous
algorithm. `ord` is the online arrival order of the covering constraints (a permutation of `J`);
`y = raiseRun inst (alg2X inst) ord` is Algorithm 2's own final dual vector (p. 121: each arriving
`yⱼ` is increased continuously *exactly while* `∑_{i ∈ S(j)} xᵢ < 1`, with `x` given by the
closed-form rule `alg2X`), and `x = alg2X inst y` its final primal vector — both computed from
the instance and the arrival order alone. The retired version took `y` as a free vector pinned
only by final covering feasibility, which admits inflated `y`. `hS` is the standing feasibility
assumption of the covering LP (every constraint involves at least one variable). Conclusions:
the covering solution is feasible (Claim (1)); the packing solution `y` is exactly feasible
(Claim (3), p. 122: non-negative and `∑_{j | i ∈ S(j)} yⱼ ≤ cᵢ`); the covering solution is
`2 ln(1+d)`-competitive against every feasible offline covering solution (Eq. (4.2),
`∂P/∂yⱼ ≤ 2 ln(1+d) · ∂D/∂yⱼ`, and weak duality); the packing solution is `2 ln(1+d)`-competitive
against every feasible offline packing solution. -/
theorem algorithm2_competitive_ratio_v2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg2X inst) ord
    let x : I → ℝ := alg2X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.log (1 + inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j) := by sorry

end OnlinePrimalDual.Framework
