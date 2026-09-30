-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_mean_busy_circuits
-- name    : KellyStochasticNetworks.erlang_mean_busy_circuits
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:49:24.663494+00:00
-- url     : https://prove2.me/theorems/a4419442-5eee-43a7-83d1-e64485f48002
-- title:
--   Exercise 1.7 — the mean number of circuits in use is $\nu(1 - E(\nu,C))$
-- statement:
--   Consider the Erlang loss link with $C$ circuits, arrival rate $\lambda > 0$ and holding-time
--   parameter $\mu > 0$, and write $\nu = \lambda/\mu$ for the traffic intensity. Let
--   $\pi = (\pi(j))_{j=0}^{C}$ be the equilibrium distribution, that is, a solution of the detailed
--   balance equations for the link's transition rates with $\sum_{j=0}^{C} \pi(j) = 1$. Then the
--   mean number of circuits in use is
--   $$\sum_{j=0}^{C} j\,\pi(j) = \nu\bigl(1 - E(\nu, C)\bigr),$$
--   where $E(\nu,C)$ is Erlang's formula.
--
--   The identity says that the carried traffic equals the offered traffic $\nu$ times the
--   probability $1 - E(\nu,C)$ that an arriving call is not blocked, which is the conservation
--   statement an operator uses to turn a measured circuit occupancy into an estimate of the
--   offered load.
--
--   **Formalization Note** The sum is over the finite state space `Fin (C + 1)`; the summand uses
--   the underlying natural number of the index, cast to a real number.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 20 (PDF p. 28), Exercise 1.7: 'Show that the mean number of circuits in use in the model leading to Erlang's formula, i.e. the mean of the equilibrium distribution pi, is nu(1 - E(nu,C)).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_mean_busy_circuits (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    ∑ j : Fin (C + 1), ((j : ℕ) : ℝ) * π j
      = (lam / mu) * (1 - erlang (lam / mu) C) := by sorry

end KellyStochasticNetworks
