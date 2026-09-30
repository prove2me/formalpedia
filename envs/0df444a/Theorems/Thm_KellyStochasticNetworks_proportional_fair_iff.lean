-- Prove2me | Theorems.Thm_KellyStochasticNetworks_proportional_fair_iff
-- name    : KellyStochasticNetworks.proportional_fair_iff
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:36:22.687788+00:00
-- url     : https://prove2.me/theorems/bb1adfac-804e-4bbf-a57e-ab4d69237a02
-- title:
--   Proposition 7.4 — the network problem and weighted proportional fairness agree
-- statement:
--   The network problem $\mathrm{network}(A,C;w)$ is to maximize $\sum_r w_r\log x_r$ over the
--   feasible flows $x\ge0$ with $\sum_{s:j\in s}x_s\le C_j$ for every resource $j$. A feasible
--   vector $x$ with every $x_r>0$ is **weighted proportionally fair** when the aggregate of
--   proportional changes to any other feasible allocation is non-positive:
--   $$\sum_r w_r\,\frac{y_r-x_r}{x_r}\;\le\;0 \qquad\text{for every feasible } y .$$
--
--   Proposition 7.4: these are the same condition. A feasible $x$ with positive components
--   maximizes $\sum_r w_r\log x_r$ over the positive feasible flows if and only if it is weighted
--   proportionally fair.
--
--   One direction is concavity of the logarithm: $\log y_r-\log x_r\le (y_r-x_r)/x_r$, so a
--   non-positive aggregate of proportional changes forces $\sum_r w_r\log y_r\le\sum_r w_r\log
--   x_r$. The other is the first-order condition: the objective changes by
--   $\sum_r w_r\,\delta x_r/x_r+o(\delta x)$ under a perturbation, so optimality gives the
--   inequality infinitesimally, and concavity extends it to non-infinitesimal variations.
--
--   The equivalence is what lets Theorem 7.6 be read as a fairness statement: the primal algorithm
--   converges to the maximizer of an objective whose first term is $\sum_r w_r\log x_r$, and
--   therefore to the proportionally fair allocation. By Remark 7.5 that allocation is also the Nash
--   bargaining solution and a market-clearing equilibrium.
--
--   **Formalization Note** The maximum is taken over the feasible set intersected with the positive
--   orthant, since $\log 0$ is not a real number and the book's optimum is interior. The fairness
--   condition is quantified over all feasible $y$, including boundary points, exactly as the book
--   states it; the quotient $(y_r-x_r)/x_r$ is meaningful there because $x_r>0$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 159-160 (PDF pp. 167-168), the definition of weighted proportional fairness and Proposition 7.4: 'We say an allocation x = (x_r, r in R) is proportionally fair if it is feasible, and if for any other feasible allocation y the aggregate of proportional changes is non-positive: sum_r (y_r - x_r)/x_r <= 0.' 'Proposition 7.4 A vector x solves network(A, C; w) if and only if it is weighted proportionally fair.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem proportional_fair_iff {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r)
    (x : Fin R → ℝ) (hxpos : ∀ r, 0 < x r) (hxfeas : x ∈ networkFeasible A C) :
    IsMaxOn (networkObjective w) (networkFeasible A C ∩ {y | ∀ r, 0 < y r}) x
      ↔ ∀ y ∈ networkFeasible A C, (∑ r, w r * ((y r - x r) / x r)) ≤ 0 := by sorry

end KellyStochasticNetworks
