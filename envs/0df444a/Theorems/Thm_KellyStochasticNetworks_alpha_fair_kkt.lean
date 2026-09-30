-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_kkt
-- name    : KellyStochasticNetworks.alpha_fair_kkt
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:50:10.766948+00:00
-- url     : https://prove2.me/theorems/8a554068-9ff8-4464-af46-ec6724f09fda
-- title:
--   Exercise 8.4 — the characterization $x_r = (w_r/\sum_{j\in r}p_j)^{1/\alpha}$
-- statement:
--   The $\alpha$-fair allocation is characterized by Karush–Kuhn–Tucker conditions. Let $q_j$ be a
--   Lagrange multiplier for the capacity constraint at resource $j$, and write
--   $p_r = \sum_{j \in r} q_j$ for the total price along route $r$. Suppose a positive rate vector $x$
--   and multipliers $q$ satisfy
--
--   1. **the stationarity condition** $x_r = \bigl(w_r/p_r\bigr)^{1/\alpha}$ for every route $r$;
--   2. **primal feasibility**: $\sum_{r : j \in r} n_r x_r \le C_j$ for every resource $j$;
--   3. **dual feasibility**: $q_j \ge 0$ for every resource $j$;
--   4. **complementary slackness**: $q_j\bigl(C_j - \sum_{r : j \in r} n_r x_r\bigr) = 0$ for every $j$
--      — a resource with a positive price is saturated.
--
--   Then the aggregate rates $X_r = n_r x_r$ maximize the $\alpha$-fair objective over the feasible
--   set.
--
--   The stationarity condition is the informative one. A route's rate depends on the network only
--   through the sum of the prices of the resources it uses, and the exponent $1/\alpha$ controls how
--   sharply a route reacts to that price: small $\alpha$ makes rates very sensitive, so capacity
--   concentrates on cheap routes and throughput is maximized, while large $\alpha$ flattens the
--   response towards max-min fairness.
--
--   **Formalization Note** The route price is introduced as a named quantity with its defining
--   identity as a hypothesis, which keeps the statement readable and matches the book's notation. The
--   conclusion is maximality of the aggregate rates over the feasible set intersected with the positive
--   orthant, since the objective involves real powers and a logarithm.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 188 (PDF p. 196): 'We can characterize the solutions of the problem (8.1) as follows. Let (p_j, j in J) be Lagrange multipliers for the constraints. Then, at the optimum, x = x(n) and p = p(n) satisfy x_r = ( w_r / sum_{j in r} p_j )^{1/alpha}, r in R, where x_r >= 0, sum_{r : j in r} n_r x_r <= C_j (primal feasibility); p_j >= 0 (dual feasibility); p_j (C_j - sum_{r : j in r} n_r x_r) = 0 (complementary slackness).' And Exercise 8.4: 'Check the claimed characterization of the solutions to the problem (8.1).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_kkt {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (x p : Fin R → ℝ) (q : Fin J → ℝ) (hxpos : ∀ r, 0 < x r)
    (hp : ∀ r, p r = ∑ j, A j r * q j) (hppos : ∀ r, 0 < p r)
    (hprimal : ∀ j, (∑ r, A j r * (n r * x r)) ≤ C j)
    (hdual : ∀ j, 0 ≤ q j)
    (hslack : ∀ j, q j * (C j - ∑ r, A j r * (n r * x r)) = 0)
    (hstat : ∀ r, x r = (w r / p r) ^ (1 / α)) :
    IsMaxOn (alphaFairObjective w n α)
      ({X | ∀ j, (∑ r, A j r * X r) ≤ C j} ∩ {X | ∀ r, 0 < X r})
      (fun r => n r * x r) := by sorry

end KellyStochasticNetworks
