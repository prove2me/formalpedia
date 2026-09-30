-- Prove2me | Theorems.Thm_MarkovDecisionProcesses_average_optimality_equation_solvable
-- name    : MarkovDecisionProcesses.average_optimality_equation_solvable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:27:15.366854+00:00
-- url     : https://prove2.me/theorems/7544b91b-3380-4ffa-9109-013feaa46d58
-- title:
--   Theorem 8.4.3 — the unichain optimality equation has a solution, with a unique gain
-- statement:
--   Consider a stationary MDP with finite state and action sets that is **unichain**: the
--   transition matrix of every deterministic stationary policy consists of a single recurrent
--   class plus a possibly empty set of transient states. Then
--
--   - (a) there exist a scalar $g$ and a function $h:S\to\mathbb R$ solving the average reward
--     optimality equation $B(g,h)=0$, that is, for every state $s$,
--     $$0=\max_{a\in A_s}\Bigl\{r(s,a)-g+\sum_{j\in S}p(j\mid s,a)\,h(j)-h(s)\Bigr\};$$
--   - (b) the scalar is unique: if $(g',h')$ is any other solution then $g=g'$.
--
--   This is Theorem 8.4.3. The source proves (a) by letting the discount factor tend to $1$ along
--   a subsequence on which the same stationary policy is discount optimal (Theorem 6.2.10 of
--   mission II), expanding the discounted value as $(1-\lambda)^{-1}g e+h+o(1)$, and passing to the
--   limit in the discounted optimality equation; the solution obtained is the gain and bias of
--   that policy. Part (b) is Theorem 8.4.1(c). The source notes that $h$ is not unique, since
--   $(g,h+ke)$ is again a solution.
--
--   **Formalization Note** Bounded rewards (Assumption 8.0.2) are automatic for a finite model
--   and are not a separate hypothesis. Unichain is the source's Section 8.3.1 classification,
--   stated through accessibility and recurrence on each $P_d$ as in the definition file. The state
--   space is assumed nonempty, as every state space of the source is: on an empty $S$ every pair
--   $(g,h)$ solves $B(g,h)=0$ vacuously, and part (b) would be false.
-- source:
--   Martin L. Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley 1994, https://doi.org/10.1002/9780470316887 — §8.4.2, printed p. 358 (PDF p. 374), Theorem 8.4.3: "Suppose S and A_s are finite Assumption 8.0.2 holds and the model is unichain. a. Then there exists a g ∈ R¹ and an h ∈ V for which 0 = max_{d∈D}{r_d − ge + (P_d − I)h}. b. If (g′, h′) is any other solution of the average reward optimality equation, then g = g′."

import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem average_optimality_equation_solvable {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (g : ℝ) (h : S → ℝ), ∀ s, optimalityResidual M g h s = 0) ∧
      ∀ (g : ℝ) (h : S → ℝ) (g' : ℝ) (h' : S → ℝ),
        (∀ s, optimalityResidual M g h s = 0) →
          (∀ s, optimalityResidual M g' h' s = 0) → g = g' := by sorry
end MarkovDecisionProcesses
