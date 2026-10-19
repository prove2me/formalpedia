-- Prove2me | Theorems.Thm_OnDemandDelivery_RouteElim_eq80_iff_eq81
-- name    : OnDemandDelivery.RouteElim.eq80_iff_eq81
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:06.824379+00:00
-- url     : https://prove2.me/theorems/de520d55-e18f-4f29-bb37-b95a3c380c9f
-- title:
--   Appendix G, Proof of Lemma 2, p. 42, (80)–(81) — for a dual optimal solution of RF1, the bound test (80) is the reduced-cost test (81)
-- statement:
--   In the routing subproblem of one period $n$ (with the standing assumptions $\alpha_{i,r},\beta_{n',r}\in\{0,1\}$), suppose the LP relaxation RF1 attains its optimal cost $\phi(\mathrm{RF1})$, and let $(\bar\mu,\bar\mu_n,\bar\nu)$ be a dual optimal solution of RF1. For every real $ub$ and every route $r$,
--   $$c_r+\sum_{n'=n+1}^N\sum_{k=0}^{\bar K}\bar\mu_{n'}k\bar z^{n'}_k-\sum_{n'=n+1}^N\beta_{n',r}\bar\mu_{n'}+\bar\mu_n(\bar K-\zeta^n_n-1)+\sum_{i\in\mathcal I^n_r}\bar\nu_i>ub \tag{80}$$
--   holds if and only if
--   $$c_r-\sum_{i\in\mathcal I^n}\alpha_{i,r}\bar\nu_i-\sum_{n'=n+1}^N\beta_{n',r}\bar\mu_{n'}-\bar\mu_n>ub-\phi(\mathrm{RF1}). \tag{81}$$
--   Here $\mathcal I^n_r=\{i\mid\alpha_{i,r}=0\}$.
--
--   The equivalence turns the dual bound of RF1$_r$ into a test on the reduced cost of $r$ in RF1, which needs only one LP solve for all routes.
--
--   **Formalization Note** "The optimal cost $\phi(\mathrm{RF1})$" is the attained minimum of the cost over the RF1 feasible set, and "dual optimal" means maximal dual objective over the dual feasible set; the equality of $\phi(\mathrm{RF1})$ with the dual objective of $(\bar\mu,\bar\mu_n,\bar\nu)$ is not assumed. The double sum is written $\sum_{n'}\bar\mu_{n'}b_{n'}$ with $b_{n'}=\sum_k k\bar z^{n'}_k$.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 42, Appendix G, Proof of Lemma 2, (80)–(81)

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting

namespace OnDemandDelivery.RouteElim

theorem eq80_iff_eq81 {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (φ : ℝ) (hφ : IsLeast (D.cost '' {θ | D.RF1Feasible θ}) φ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualOptimal μ μn ν)
    (ub : ℝ) (r : R) :
    ub < D.c r + D.rf1rBound r μ μn ν ↔ ub - φ < D.reducedCost μ μn ν r := by sorry

end OnDemandDelivery.RouteElim
