-- Prove2me | Theorems.Thm_KellyStochasticNetworks_primal_utility_deriv
-- name    : KellyStochasticNetworks.primal_utility_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:37:24.036396+00:00
-- url     : https://prove2.me/theorems/d9843b74-48da-46e8-97a2-ac710217ed3a
-- title:
--   Theorem 7.6 (proof) — the partial derivative of the Lyapunov function
-- statement:
--   For the Lyapunov function
--   $$U(x)=\sum_r w_r\log x_r-\sum_j\int_0^{\sum_{s:j\in s}x_s}p_j(y)\,dy$$
--   with each $p_j$ continuous, and for any $x$ in the positive orthant, the partial derivative in
--   the $r$-th coordinate is
--   $$\frac{\partial U}{\partial x_r}(x)=\frac{w_r}{x_r}-\sum_{j\in r}p_j\Bigl(\sum_{s:j\in s}x_s\Bigr).$$
--
--   Two things follow, and both are used in the proof of Theorem 7.6. Setting these derivatives to
--   zero identifies the maximizer of $U$, since $U$ is strictly concave. And the resulting
--   stationarity condition $w_r/x_r=\sum_{j\in r}p_j(\cdot)$ is, after multiplying by $x_r$,
--   exactly the condition that the right-hand side of the primal algorithm (7.5) vanishes — so the
--   maximizer of $U$ is an equilibrium point of the dynamics.
--
--   The derivative of the second term is where the fundamental theorem of calculus enters: the
--   load on resource $j$ depends on $x_r$ with coefficient $A_{jr}$, so differentiating
--   $\int_0^{\text{load}}p_j$ returns $A_{jr}\,p_j(\text{load})$, and summing over $j$ gives the
--   sum over the resources of route $r$.
--
--   **Formalization Note** The partial derivative is stated as an ordinary derivative in the $r$-th
--   coordinate, with the others held fixed, so no partial-derivative API is presupposed. Continuity
--   of $p_j$ is what makes $\int_0^{y}p_j$ differentiable with derivative $p_j(y)$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 164 (PDF p. 172), in the proof of Theorem 7.6: 'Moreover, U(x) is continuously differentiable with (partial / partial x_r) U(x) = w_r/x_r - sum_{j in r} p_j( sum_{s : j in s} x_s ), and setting these derivatives to zero identifies the maximum, x say. The derivative (7.5) is zero at x, and hence x is an equilibrium point.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_utility_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hp : ∀ j, Continuous (p j)) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => primalUtility A w p (Function.update x r t))
      (w r / x r - ∑ j, A j r * p j (linkFlow A x j)) (x r) := by sorry

end KellyStochasticNetworks
