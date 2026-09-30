-- Prove2me | Theorems.Thm_KellyStochasticNetworks_primal_equilibrium
-- name    : KellyStochasticNetworks.primal_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:38:00.682268+00:00
-- url     : https://prove2.me/theorems/ac6b14fc-f884-4b13-8fb1-6ede30b991ac
-- title:
--   Theorem 7.6 (proof) — a stationary point of $U$ is an equilibrium of the primal algorithm
-- statement:
--   For a flow vector $x$ in the positive orthant and gains $\kappa_r>0$, the following are
--   equivalent:
--
--   1. $x$ is a stationary point of the Lyapunov function, $\dfrac{w_r}{x_r}-\sum_{j\in r}p_j(\cdot)=0$
--      for every route $r$;
--   2. $x$ is an equilibrium of the primal algorithm, $\kappa_r\bigl(w_r-x_r\sum_{j\in r}p_j(\cdot)\bigr)=0$
--      for every route $r$.
--
--   The two differ by the factor $\kappa_r x_r$, which is positive, so on the positive orthant they
--   are the same condition. Combined with strict concavity, this is the step of Theorem 7.6 that
--   identifies the maximizer of $U$ with the unique rest point of the dynamics — the reason the
--   decentralized algorithm can be said to solve the optimization problem at all, before any
--   question of convergence arises.
--
--   **Formalization Note** Positivity of every $x_r$ and of every gain $\kappa_r$ is what makes the
--   equivalence hold in both directions; without them the second condition is strictly weaker.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 164 (PDF p. 172), in the proof of Theorem 7.6: 'setting these derivatives to zero identifies the maximum, x say. The derivative (7.5) is zero at x, and hence x is an equilibrium point.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_equilibrium {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) :
    (∀ r, w r / x r - ∑ j, A j r * p j (linkFlow A x j) = 0)
      ↔ ∀ r, primalDrift A w κ p x r = 0 := by sorry

end KellyStochasticNetworks
