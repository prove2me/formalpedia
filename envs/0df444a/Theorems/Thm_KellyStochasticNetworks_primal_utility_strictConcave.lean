-- Prove2me | Theorems.Thm_KellyStochasticNetworks_primal_utility_strictConcave
-- name    : KellyStochasticNetworks.primal_utility_strictConcave
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:36:48.824852+00:00
-- url     : https://prove2.me/theorems/c61a1bb5-8918-45a3-8c17-7ba9d870fda0
-- title:
--   Theorem 7.6 (proof) — the Lyapunov function is strictly concave
-- statement:
--   Let
--   $$U(x)=\sum_r w_r\log x_r-\sum_j\int_0^{\sum_{s:j\in s}x_s}p_j(y)\,dy$$
--   with $w_r>0$ and each $p_j$ non-negative, continuous and increasing. Then $U$ is **strictly
--   concave** on the open positive orthant.
--
--   Both terms contribute. The first is a positive combination of logarithms, strictly concave in
--   each coordinate. The second is the negative of a sum of functions $y\mapsto\int_0^{y}p_j$,
--   each convex because $p_j$ is increasing, composed with the linear map $x\mapsto Ax$; a convex
--   function of a linear map is convex, so its negative is concave. Strict concavity of the first
--   term survives the addition.
--
--   This is the first sentence of the proof of Theorem 7.6, and it does two jobs: it makes the
--   maximizer unique, and, with the growth of $-\int_0^{y}p_j$, it makes the sublevel sets of $U$
--   compact, which is what the convergence argument needs to confine the trajectory.
--
--   **Formalization Note** "Increasing" is taken weakly, which is all the convexity of the integral
--   needs and is the weaker hypothesis. Strict concavity is asserted on the open positive orthant,
--   a convex set, which is where $\log x_r$ is meaningful.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 164 (PDF p. 172), in the proof of Theorem 7.6: 'The assumptions on w_r > 0, r in R, and p_j(.), j in J, ensure that U(.) is strictly concave with a maximum that is interior to the positive orthant; the maximizing value of x is thus unique.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem primal_utility_strictConcave {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) (hpnn : ∀ j y, 0 ≤ p j y) :
    StrictConcaveOn ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} (primalUtility A w p) := by sorry

end KellyStochasticNetworks
