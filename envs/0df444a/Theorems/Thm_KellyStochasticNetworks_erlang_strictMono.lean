-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_strictMono
-- name    : KellyStochasticNetworks.erlang_strictMono
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:44:33.335026+00:00
-- url     : https://prove2.me/theorems/19802893-c7c5-4644-9351-a60914ac0107
-- title:
--   Erlang's formula and the utilization are strictly increasing in the offered load
-- statement:
--   Let $E(\nu, C)$ be Erlang's formula, the blocking probability of a link with $C$ circuits
--   offered traffic of intensity $\nu$. For $C \ge 1$, both
--   $$\nu \mapsto E(\nu, C) \qquad\text{and}\qquad \nu \mapsto \nu\bigl(1 - E(\nu,C)\bigr)$$
--   are strictly increasing on $\nu > 0$. The second is the **utilization**, the mean number of
--   circuits in use, by Exercise 1.7.
--
--   Both statements are used in the proof of Theorem 3.20. The function $U(y, C)$ defined there by
--   the implicit relation $U(-\log(1 - E(\nu,C)), C) = \nu(1 - E(\nu,C))$ is the utilization
--   expressed in terms of $y = -\log(1-E)$; that $U$ is well defined and strictly increasing in $y$
--   is exactly these two monotonicities, and it is what makes $\int_0^y U(z,C)\,dz$ strictly convex
--   and hence the revised dual problem (3.8) uniquely solvable.
--
--   **Formalization Note** The restriction $C \ge 1$ is expressed by stating the result at $C+1$
--   for an arbitrary natural number $C$. It cannot be dropped: $E(\nu, 0) = 1$ identically, so at
--   $C = 0$ both functions are constant. Strict monotonicity is asserted on the open half-line
--   $\nu > 0$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 68 (PDF p. 76), in the proof of Theorem 3.20: 'As both the utilization nu(1 - E(nu,C)) and the blocking probability E(nu,C) are strictly increasing functions of nu, the function U(y,C) is a strictly increasing function of y. Therefore, the function int_0^y U(z,C) dz is a strictly convex function of y.' The utilization is Exercise 1.7, p. 20. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem erlang_strictMono (C : ℕ) :
    StrictMonoOn (fun ν : ℝ => erlang ν (C + 1)) (Set.Ioi 0)
      ∧ StrictMonoOn (fun ν : ℝ => ν * (1 - erlang ν (C + 1))) (Set.Ioi 0) := by sorry

end KellyStochasticNetworks
