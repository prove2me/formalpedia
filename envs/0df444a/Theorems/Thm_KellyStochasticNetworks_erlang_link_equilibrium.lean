-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_link_equilibrium
-- name    : KellyStochasticNetworks.erlang_link_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:48:52.715669+00:00
-- url     : https://prove2.me/theorems/8ba51e3a-0438-4434-8a95-458e5314c339
-- title:
--   The equilibrium distribution of the Erlang loss link
-- statement:
--   Consider the Erlang loss link with $C$ parallel circuits, calls arriving at rate
--   $\lambda > 0$ and holding times exponential of parameter $\mu > 0$, whose transition rates on
--   the state space $\{0,1,\dots,C\}$ are
--   $$q(j,j+1) = \lambda \quad (j < C), \qquad q(j,j-1) = j\mu \quad (j \ge 1).$$
--
--   If a collection of numbers $\pi = (\pi(j))_{j=0}^{C}$ satisfies the detailed balance equations
--   for these rates, then for every state $j$
--   $$\pi(j) = \frac{(\lambda/\mu)^{j}}{j!}\,\pi(0).$$
--
--   This is the solution of the detailed balance recursion on p. 18 of the book. It determines the
--   equilibrium distribution up to the single unknown $\pi(0)$, which the normalization
--   $\sum_{j} \pi(j) = 1$ then fixes. No normalization is assumed here, so the statement applies
--   to any solution of the detailed balance equations, normalized or not.
--
--   **Formalization Note** The state space is `Fin (C + 1)` and the exponent $j$ is the underlying
--   natural number of that index, so the factorial is the ordinary factorial of a natural number.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 18 (PDF p. 26): 'We try to solve the detailed balance equations: pi(j-1) q(j-1,j) = pi(j) q(j,j-1) => pi(j) = (lambda / (mu j)) pi(j-1) = ... = (lambda/mu)^j (1/j!) pi(0).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_link_equilibrium (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C)) (j : Fin (C + 1)) :
    π j = (lam / mu) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ) * π 0 := by sorry

end KellyStochasticNetworks
