-- Prove2me | Theorems.Thm_MarkovDecisionProcesses_improving_rule_average_optimal
-- name    : MarkovDecisionProcesses.improving_rule_average_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:28:24.647403+00:00
-- url     : https://prove2.me/theorems/079f5bfa-007e-441b-a864-c1c4d3188862
-- title:
--   Theorem 8.4.4 — an h*-improving decision rule gives an average optimal stationary policy
-- statement:
--   Consider a stationary MDP with finite state and action sets. Suppose a scalar $g^*$ and a
--   function $h^*:S\to\mathbb R$ satisfy the optimality equation $B(g^*,h^*)=0$, and let $d^*$ be an
--   $h^*$-**improving** decision rule: at every state $s$, $d^*(s)$ attains
--   $\max_{a\in A_s}\{r(s,a)+\sum_jp(j\mid s,a)h^*(j)\}$. Then the stationary policy $(d^*)^\infty$
--   is **average optimal**: its lim inf average reward dominates the lim sup average reward of
--   every history-dependent randomized policy at every state.
--
--   This is Theorem 8.4.4, the identification of an optimal policy from a solution of the
--   optimality equation. Since $d^*$ attains the maximum, $r_{d^*}-g^*e+(P_{d^*}-I)h^*=0$, so by
--   Corollary 8.2.7 the gain of $(d^*)^\infty$ is $g^*$, and Theorem 8.4.1(c) says $g^*$ is the
--   optimal gain. The source's Example 8.4.3 shows the converse fails: a policy can be average
--   optimal without being $h^*$-improving.
--
--   **Formalization Note** No unichain hypothesis is imposed, matching the printed statement:
--   the constant solution $(g^*,h^*)$ is the hypothesis, and on a finite chain the identity
--   $r_d-g^*e+(P_d-I)h^*=0$ forces the gain of $d^\infty$ to be $g^*$ whatever the chain
--   structure. Admissibility of $d^*(s)$ is part of being improving.
-- source:
--   Martin L. Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley 1994, https://doi.org/10.1002/9780470316887 — §8.4.3, printed p. 361 (PDF p. 377), Theorem 8.4.4: "Suppose there exists a scalar g*, and an h* ∈ V for which B(g*, h*) = 0. Then, if d* is h*-improving, (d*)^∞ is average optimal."

import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem improving_rule_average_optimal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (gstar : ℝ) (hstar : S → ℝ)
    (hB : ∀ s, optimalityResidual M gstar hstar s = 0)
    (d : S → A) (hd : IsImproving M hstar d) :
    IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by sorry
end MarkovDecisionProcesses
