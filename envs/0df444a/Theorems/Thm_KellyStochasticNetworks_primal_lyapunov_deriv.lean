-- Prove2me | Theorems.Thm_KellyStochasticNetworks_primal_lyapunov_deriv
-- name    : KellyStochasticNetworks.primal_lyapunov_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:38:31.279188+00:00
-- url     : https://prove2.me/theorems/ed9e96e9-4954-4f25-8e37-66a0957750b5
-- title:
--   Equation (7.7) — $U$ increases along every trajectory
-- statement:
--   Let $x(\cdot)$ be a trajectory of the primal algorithm staying in the positive orthant, so that
--   at time $t$
--   $$\frac{d}{dt}x_r(t)=\kappa_r\Bigl(w_r-x_r(t)\sum_{j\in r}p_j\Bigl(\sum_{s:j\in s}x_s(t)\Bigr)\Bigr)
--     \qquad\text{for every } r .$$
--   Then $t\mapsto U(x(t))$ is differentiable with
--   $$\frac{d}{dt}U(x(t))=\sum_r\frac{\kappa_r}{x_r(t)}
--     \Bigl(w_r-x_r(t)\sum_{j\in r}p_j\Bigl(\sum_{s:j\in s}x_s(t)\Bigr)\Bigr)^2\;\ge\;0 .$$
--
--   This is equation (7.7), and it is what makes $U$ a Lyapunov function. The derivation is the
--   chain rule: each term of $\sum_r(\partial U/\partial x_r)\,\dot x_r$ is
--   $\bigl(w_r/x_r-\sum_{j\in r}p_j\bigr)\cdot\kappa_r\bigl(w_r-x_r\sum_{j\in r}p_j\bigr)$, and
--   factoring $1/x_r$ out of the first bracket turns the product into a square. Non-negativity is
--   then immediate, and the derivative vanishes exactly at an equilibrium.
--
--   The book is careful about what this does *not* prove. A strictly increasing Lyapunov function
--   does not by itself give convergence — the derivative could become small fast enough for the
--   trajectory to stall short of the maximum — and closing that gap requires the compactness
--   argument that is the substance of Theorem 7.6.
--
--   **Formalization Note** A trajectory is a differentiable function of real time whose derivative
--   equals the primal drift pointwise; positivity along the trajectory is a hypothesis rather than
--   derived from the dynamics. The conclusion asserts differentiability and the value of the
--   derivative together, and separately its non-negativity.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 164 (PDF p. 172), equation (7.7) in the proof of Theorem 7.6: 'Further, d/dt U(x(t)) = sum_{r in R} (partial U / partial x_r) (d/dt) x_r(t) = sum_{r in R} (kappa_r / x_r(t)) ( w_r - x_r(t) sum_{j in r} p_j( sum_{s : j in s} x_s(t) ) )^2 >= 0, (7.7) with equality only at x.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_lyapunov_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j))
    (x : ℝ → Fin R → ℝ) (t : ℝ) (hpos : ∀ r, 0 < x t r)
    (hode : ∀ r, HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    HasDerivAt (fun s => primalUtility A w p (x s))
        (∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2) t
      ∧ 0 ≤ ∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by sorry

end KellyStochasticNetworks
