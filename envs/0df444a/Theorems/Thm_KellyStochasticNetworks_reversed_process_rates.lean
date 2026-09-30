-- Prove2me | Theorems.Thm_KellyStochasticNetworks_reversed_process_rates
-- name    : KellyStochasticNetworks.reversed_process_rates
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:46:57.308277+00:00
-- url     : https://prove2.me/theorems/85fffc0a-e45c-476a-bd3c-1705bc378b46
-- title:
--   Proposition 1.1 — the time-reversed process keeps $\pi$ in equilibrium
-- statement:
--   Let $(X(t), t \in \mathbb{R})$ be a stationary Markov process on a finite state space $S$ with
--   transition rates $q$ and a strictly positive equilibrium distribution $\pi$, so that $\pi$
--   satisfies the equilibrium equations for $q$. Proposition 1.1 of Kelly and Yudovina states that
--   the reversed process $Y(t) = X(-t)$ is again a stationary Markov process, with the same
--   equilibrium distribution $\pi$ and with transition rates
--   $$q'(j,k) = \frac{\pi(k)\,q(k,j)}{\pi(j)}.$$
--
--   The two algebraic assertions that content amounts to, and which Exercise 1.4 asks the reader
--   to check, are formalized here:
--
--   1. the reversed rates have the same total rate out of every state,
--   $$\sum_{k \in S} q'(j,k) = \sum_{k \in S} q(j,k) \qquad \text{for all } j \in S,$$
--   so a jump of the reversed process occurs at the same rate as a jump of the original;
--   2. $\pi$ satisfies the equilibrium equations for $q'$, so $\pi$ is again an equilibrium
--   distribution for the reversed process.
--
--   Together these say that $q'$ is a legitimate rate matrix with the same holding-time
--   parameters as $q$, and that reversing a stationary process does not disturb its equilibrium
--   distribution.
--
--   **Formalization Note** The state space is taken finite so that every sum appearing is a finite
--   sum; the positivity of $\pi$ is what makes the quotient defining $q'$ meaningful.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 16-17 (PDF pp. 24-25), Proposition 1.1 and Exercise 1.4: 'Check that the distribution (pi(j), j in S) and the transition rates (q'(j,k), j,k in S) found in Proposition 1.1 satisfy the equilibrium equations.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem reversed_process_rates {S : Type*} [Fintype S] (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) (h : FullBalance π q) :
    (∀ j : S, (∑' k : S, reversedRates π q j k) = ∑' k : S, q j k) ∧
      FullBalance π (reversedRates π q) := by sorry

end KellyStochasticNetworks
