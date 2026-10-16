-- Prove2me | Theorems.Thm_OnDemandDelivery_RouteElim_lemma_2
-- name    : OnDemandDelivery.RouteElim.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:14.08647+00:00
-- url     : https://prove2.me/theorems/298a869e-3d55-443a-83fe-54038eacf9e0
-- title:
--   Lemma 2, p. 19 — a route whose reduced cost exceeds ub − φ(RF1) is in no optimal solution of SF1
-- statement:
--   Consider the single-period routing subproblem SF1 of the Benders decomposition of Liu and Luo: in period $n$, choose a set of routes from the finite route set $\mathcal R^n$ (binary $\theta_r$) of minimum total cost $\sum_r\theta_r c_r$, so that every current location $i\in\mathcal I^n$ is served exactly once ($\sum_r\alpha_{i,r}\theta_r=1$), at most $\bar K-\zeta^n_n$ routes are used, and in every future period $n'$ at most $\sum_{k=0}^{\bar K}k\bar z^{n'}_k$ chosen routes are still running. Here $\alpha_{i,r},\beta_{n',r}\in\{0,1\}$. Let RF1 be its LP relaxation ($\theta\ge0$, covering rows $\ge 1$).
--
--   Let $ub$ be an upper bound of SF1 (at least the cost of every optimal solution), let $\phi(\mathrm{RF1})$ be the optimal cost of RF1, let $(\mu,\mu_n,\nu)$ be a dual optimal solution of RF1 (dual variables $\mu_{n'}$, $\mu_n$, $\nu_i$ of the rows (25), (19), (26)), and let $r\in\mathcal R^n$. If
--   $$c_r-\sum_{i\in\mathcal I^n}\alpha_{i,r}\nu_i-\sum_{n'=n+1}^N\beta_{n',r}\mu_{n'}-\mu_n>ub-\phi(\mathrm{RF1}),$$
--   then $\theta_r=0$ in every optimal solution $\theta$ of SF1.
--
--   In words: once RF1 is solved, every route whose reduced cost exceeds the gap $ub-\phi(\mathrm{RF1})$ can be discarded before SF1 is solved exactly. This is the pruning rule of the paper's route enumeration algorithm.
--
--   **Formalization Note** $\phi(\mathrm{RF1})$ is the attained minimum of RF1 (an `IsLeast` hypothesis); "dual optimal" is maximality of the dual objective over the dual feasible set, with the standard sign convention $\mu_{n'}\le0$, $\mu_n\le0$, $\nu_i\ge0$ (the paper does not print it). "An upper bound $ub$ of SF1" is read in its weakest form, $ub\ge$ the cost of every optimal solution. The standing assumptions also include $\bar z^{n'}_k\in\{0,1\}$ and $\sum_k\bar z^{n'}_k=1$ ((17), (21)). Routes, locations and future periods are arbitrary finite types.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 19, Lemma 2, (33)

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting

namespace OnDemandDelivery.RouteElim

theorem lemma_2 {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (φ : ℝ) (hφ : IsLeast (D.cost '' {θ | D.RF1Feasible θ}) φ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualOptimal μ μn ν)
    (r : R) (h33 : ub - φ < D.reducedCost μ μn ν r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by sorry

end OnDemandDelivery.RouteElim
