-- Prove2me | Theorems.Thm_OnDemandDelivery_RouteElim_rf1r_dual_bound
-- name    : OnDemandDelivery.RouteElim.rf1r_dual_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:11.77136+00:00
-- url     : https://prove2.me/theorems/1531ec96-8af3-488e-827a-a570e5263d63
-- title:
--   Appendix G, Proof of Lemma 2, p. 42 — the restriction of a dual feasible solution of RF1 bounds φ(SF1_r) from below
-- statement:
--   In the routing subproblem of one period $n$, let $(\bar\mu,\bar\mu_n,\bar\nu)$ be a dual feasible solution of the LP relaxation RF1: $\bar\mu_{n'}\le 0$, $\bar\mu_n\le 0$, $\bar\nu_i\ge 0$, and $\sum_i\alpha_{i,r'}\bar\nu_i+\sum_{n'}\beta_{n',r'}\bar\mu_{n'}+\bar\mu_n\le c_{r'}$ for every route $r'$. Fix a route $r$ and let $\mathcal I^n_r=\{i\mid \alpha_{i,r}=0\}$. Then:
--
--   1. $(\bar\mu,\bar\mu_n,\{\bar\nu_i\}_{i\in\mathcal I^n_r})$ is a dual feasible solution of the restricted LP RF1$_r$ (75)–(79);
--   2. its dual objective
--   $$B_r=\sum_{n'=n+1}^N\sum_{k=0}^{\bar K}\bar\mu_{n'}k\bar z^{n'}_k-\sum_{n'=n+1}^N\beta_{n',r}\bar\mu_{n'}+\bar\mu_n(\bar K-\zeta^n_n-1)+\sum_{i\in\mathcal I^n_r}\bar\nu_i$$
--   is at most the cost of every feasible solution of RF1$_r$;
--   3. hence $B_r\le\phi(\mathrm{SF1}_r)$, the optimal cost of the restricted integer program.
--
--   This bound is the computable substitute for $\phi(\mathrm{SF1}_r)$ in the elimination test (74).
--
--   **Formalization Note** The page assumes $(\bar\mu,\bar\nu)$ dual optimal for RF1; the statement assumes only dual feasibility, which is all the argument needs, so it is a strengthening. The inequality $B_r\le\phi(\mathrm{SF1}_r)$ is stated in the extended reals; it holds trivially when SF1$_r$ is infeasible. The double sum is written $\sum_{n'}\bar\mu_{n'}b_{n'}$ with $b_{n'}=\sum_k k\bar z^{n'}_k$.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, p. 42, Appendix G, Proof of Lemma 2, after (75)–(79)

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting

namespace OnDemandDelivery.RouteElim

theorem rf1r_dual_bound {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualFeasible μ μn ν) (r : R) :
    D.RF1rDualFeasible r μ μn ν ∧
      (∀ θ', D.RF1rFeasible r θ' → D.rf1rBound r μ μn ν ≤ D.cost θ') ∧
      ((D.rf1rBound r μ μn ν : ℝ) : EReal) ≤ D.phiSF1r r := by sorry

end OnDemandDelivery.RouteElim
