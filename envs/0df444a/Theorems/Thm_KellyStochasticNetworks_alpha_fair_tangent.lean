-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_tangent
-- name    : KellyStochasticNetworks.alpha_fair_tangent
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:50:31.05443+00:00
-- url     : https://prove2.me/theorems/b31a7246-53e6-44b2-a316-d8174bb35387
-- title:
--   Equation (8.5) — the tangent plane at any feasible point lies above the optimum
-- statement:
--   Let $X$ maximize the $\alpha$-fair objective $G$ over the feasible set, and let $U$ be any other
--   feasible point with positive components. Then
--   $$\sum_r w_r n_r^{\alpha}\,U_r^{-\alpha}\,\bigl(U_r - X_r\bigr) \;\le\; 0 .$$
--
--   The left-hand side is $G'(U)\cdot(U-X)$, since $G'(U)_r = w_r n_r^{\alpha}U_r^{-\alpha}$. The
--   inequality is concavity read backwards: the tangent plane to $G$ at $U$ lies above $G$
--   everywhere, so $G(X) \le G(U) + G'(U)\cdot(X-U)$, and since $X$ is the maximum,
--   $G(U) - G(X) \le 0$; chaining the two gives $G'(U)\cdot(U-X) \le G(U)-G(X) \le 0$.
--
--   This is equation (8.5), and it is the entire mechanism of the stability proof. The drift of the
--   Lyapunov function has exactly the shape $\sum_r w_r n_r^{\alpha}U_r^{-\alpha}(U_r - X_r)$ with
--   $U$ the load vector $\rho$; the inequality applies as soon as $\rho$ is feasible, which is what
--   the stability condition (8.2) asserts. The choice of $U$ is the whole idea — no term-by-term
--   estimate would work, because some routes are over-served and some under-served.
--
--   **Formalization Note** The inequality is stated in the form it is used, as a bound on a sum
--   rather than as an inner product, and for a fixed feasible $U$ rather than universally. Positivity
--   of $U$ is needed for the real power $U_r^{-\alpha}$ to be the intended quantity.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 190-191 (PDF pp. 198-199), equation (8.5) and Figure 8.1: 'Since G is concave, for every U inside the feasible region of (8.4) G'(U) . (U - X) <= G(U) - G(X) <= 0, (8.5)' and 'Let X be the optimum and let U be another point in the feasible region of (8.4). Since G(.) is concave, the tangent plane at U lies above G(.), so G(X) <= G(U) + G'(U) . (X - U).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_tangent {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X U : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hUpos : ∀ r, 0 < U r)
    (hXfeas : X ∈ networkFeasible A C) (hUfeas : U ∈ networkFeasible A C)
    (hmax : IsMaxOn (alphaFairObjective w n α)
      (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X) :
    (∑ r, w r * n r ^ α * U r ^ (-α) * (U r - X r)) ≤ 0 := by sorry

end KellyStochasticNetworks
