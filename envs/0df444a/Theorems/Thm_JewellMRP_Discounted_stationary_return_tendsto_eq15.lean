-- Prove2me | Theorems.Thm_JewellMRP_Discounted_stationary_return_tendsto_eq15
-- name    : JewellMRP.Discounted.stationary_return_tendsto_eq15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:00:34.77999+00:00
-- url     : https://prove2.me/theorems/3ffa9173-dddc-44d5-a279-fc18476948b8
-- title:
--   Eq. (15), p. 945 — the return of a stationary policy satisfies the simultaneous equations (15)
-- statement:
--   Let a Markov-renewal program be given, let $\alpha > 0$, let $d$ be a stationary policy and let $V^0$ be any vector of boundary rewards. Write $V^d_i(n)$ for the $n$-step discounted return of $d$ from state $i$ with boundary rewards $V^0$. Then $V^d(n)$ converges as $n \to \infty$ to a vector $v$ satisfying
--   $$
--   v_i = \rho^{d(i)}_i(\alpha) + \sum_{j} p^{d(i)}_{ij}\,\tilde f^{d(i)}_{ij}(\alpha)\, v_j \qquad \text{for all } i .
--   $$
--
--   The paper writes: "the return from every stationary policy in (14) must satisfy the simultaneous equations (15)". The return in (14) is the limit of the $n$-step returns, so the statement asserts that this limit exists, whatever the boundary rewards, and solves (15). Together with Claim (a) it identifies the solution of (15) with the infinite-step return of $d$.
--
--   **Formalization Note** The limit's existence is a conclusion, not an assumption. Boundary rewards are arbitrary.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 945, Eq. (15)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Eq. (15), p. 945: the `n`-step return of a stationary policy `d` converges, for every
choice of boundary rewards, to a solution of the equations (15) of `d`. -/
theorem stationary_return_tendsto_eq15 {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) (V0 : S → ℝ) :
    ∃ v : S → ℝ, SolvesEval M α d v ∧
      Tendsto (fun n => policyReturn M α (fun _ => d) V0 n) atTop (𝓝 v) := by sorry

end JewellMRP.Discounted
