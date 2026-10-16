-- Prove2me | Theorems.Thm_OnDemandDelivery_RouteElim_eq74
-- name    : OnDemandDelivery.RouteElim.eq74
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:06.6542+00:00
-- url     : https://prove2.me/theorems/d67e0a84-21be-4bc5-8a0e-adc9fd4ce17b
-- title:
--   Appendix G, Proof of Lemma 2, p. 42, (74) — if c_r + φ(SF1_r) > ub, route r is in no optimal solution of SF1
-- statement:
--   Consider the routing subproblem SF1 of one period $n$, with routes $\mathcal R^n$, costs $c_r$, coverage coefficients $\alpha_{i,r}\in\{0,1\}$ and future-period coefficients $\beta_{n',r}\in\{0,1\}$. For a route $r$, let SF1$_r$ be SF1 restricted to the routes covering only locations $i$ with $\alpha_{i,r}=0$, with right-hand sides reduced by $r$'s own use, and let $\phi(\mathrm{SF1}_r)\in\mathbb R\cup\{+\infty\}$ be its optimal cost ($+\infty$ if SF1$_r$ is infeasible).
--
--   Let $ub$ be a real number that is at least the cost of every optimal solution of SF1. If
--   $$c_r+\phi(\mathrm{SF1}_r)>ub,$$
--   then $\theta_r=0$ for every optimal solution $\theta$ of SF1.
--
--   This is the exact elimination test behind Lemma 2: it is expensive because it needs the optimal cost of an integer program per route, and Lemma 2 replaces $\phi(\mathrm{SF1}_r)$ by an LP dual bound.
--
--   **Formalization Note** The sum $c_r+\phi(\mathrm{SF1}_r)$ is taken in the extended reals, so the test holds automatically when SF1$_r$ is infeasible. "An upper bound $ub$ of problem SF1" is read in its weakest form: $ub$ is at least the cost of every optimal solution (equivalently, $ub\ge\phi(\mathrm{SF1})$ whenever SF1 is feasible); no feasible solution of cost at most $ub$ is required. The page writes $\mathcal R_n$ for $\mathcal R^n$.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 42, Appendix G, Proof of Lemma 2, (74)

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting

namespace OnDemandDelivery.RouteElim

theorem eq74 {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (r : R) (h74 : (ub : EReal) < (D.c r : EReal) + D.phiSF1r r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by sorry

end OnDemandDelivery.RouteElim
