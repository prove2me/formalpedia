-- Prove2me | Theorems.Thm_KellyStochasticNetworks_primal_global_stability
-- name    : KellyStochasticNetworks.primal_global_stability
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:39:04.552835+00:00
-- url     : https://prove2.me/theorems/b5bf1a53-e417-4bf8-8d5d-9dfc547af223
-- title:
--   Theorem 7.6 — global stability of the primal algorithm
-- statement:
--   Consider a network with $J$ resources and $R$ routes, link-route incidence matrix $A$, weights
--   $w_r>0$, gains $\kappa_r>0$, and congestion functions $p_j$ that are non-negative, continuous,
--   increasing and not identically zero. The **primal algorithm** is the differential equation
--   $$\frac{d}{dt}x_r(t)=\kappa_r\Bigl(w_r-x_r(t)\sum_{j\in r}p_j\Bigl(\sum_{s:j\in s}x_s(t)\Bigr)\Bigr),
--     \qquad r\in\mathcal{R},$$
--   and its Lyapunov function is
--   $$U(x)=\sum_r w_r\log x_r-\sum_j\int_0^{\sum_{s:j\in s}x_s}p_j(y)\,dy .$$
--
--   Let $\bar x$ be a point of the positive orthant at which the drift vanishes, that is
--   $w_r=\bar x_r\sum_{j\in r}p_j\bigl(\sum_{s:j\in s}\bar x_s\bigr)$ for every $r$. Then two
--   things hold.
--
--   1. $\bar x$ maximizes $U$ over the positive orthant.
--   2. Every trajectory of the primal algorithm that starts in the positive orthant and stays there
--      converges to $\bar x$ as $t\to\infty$.
--
--   This is Theorem 7.6, and it is the chapter's central claim: a control rule in which no
--   participant knows the network topology, and each source sees only its own rate and the
--   congestion signals reaching it, drives the whole system to the unique maximizer of a global
--   utility. Because the first term of $U$ is $\sum_r w_r\log x_r$, that maximizer is the weighted
--   proportionally fair allocation, so the protocol's limit is a fairness criterion rather than an
--   accident of the dynamics.
--
--   The first conclusion is strict concavity plus stationarity. The second is the harder half: $U$
--   increases along trajectories by equation (7.7), but that alone leaves open whether the
--   trajectory might stall short of $\bar x$, and ruling that out needs the compactness of the
--   sublevel set $\{x:U(x)\ge U(x(0))\}$ together with a uniform lower bound on the derivative away
--   from $\bar x$.
--
--   **Formalization Note** A trajectory is a differentiable function of real time whose derivative
--   equals the primal drift at every non-negative time, with positivity along the trajectory
--   assumed rather than derived; invariance of the positive orthant under the dynamics is a
--   separate statement. The equilibrium $\bar x$ is given by its stationarity condition rather than
--   by an existence claim, and that it is the maximizer is part of the conclusion, so nothing is
--   assumed about it that is not also proved.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 163 (PDF p. 171), Theorem 7.6 (Global stability): 'The strictly concave function U(x) = sum_{r in R} w_r log x_r - sum_{j in J} int_0^{ sum_{s : j in s} x_s } p_j(y) dy is a Lyapunov function for the primal algorithm. The unique value maximizing U(x) is an equilibrium point of the system, to which all trajectories converge.' The primal algorithm (7.5)-(7.6) is on p. 162. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_global_stability {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hw : ∀ r, 0 < w r) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j))
    (hpnn : ∀ j y, 0 ≤ p j y) (hpne : ∀ j, ∃ y, p j y ≠ 0)
    (xbar : Fin R → ℝ) (hbarpos : ∀ r, 0 < xbar r)
    (hbar : ∀ r, w r = xbar r * ∑ j, A j r * p j (linkFlow A xbar j))
    (x : ℝ → Fin R → ℝ) (hxpos : ∀ t, 0 ≤ t → ∀ r, 0 < x t r)
    (hode : ∀ t, 0 ≤ t → ∀ r,
      HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    IsMaxOn (primalUtility A w p) {y : Fin R → ℝ | ∀ r, 0 < y r} xbar
      ∧ Filter.Tendsto x Filter.atTop (nhds xbar) := by sorry

end KellyStochasticNetworks
