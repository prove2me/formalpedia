-- Prove2me | Theorems.Thm_LostSalesRQ_main_theorem
-- name    : LostSalesRQ.main_theorem
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:34:02.861026+00:00
-- url     : https://prove2.me/theorems/054cb9cb-33f2-47b5-a79d-e5d6c2f768a8
-- title:
--   Theorem 1: zero-setup and full-cost guarantees, tightness of $\sqrt2$
-- statement:
--   This is Theorem 1 of the paper, in full. Let $\lambda,L,h,p,K\ge0$ be the demand rate, lead time, holding cost rate, lost-sales penalty and fixed ordering cost of the continuous-review lost-sales system with unit Poisson demand, let $C(\pi)$ be the long-run average cost of an admissible policy and $\mathrm{OPT}$ the infimum over all admissible policies.
--
--   1. **Full-cost guarantee.** For every nonnegative $(\lambda,L,h,p,K)$ and every demand environment of rate $\lambda$,
--   $$\inf_{\pi\in\Pi_{\rm rQ}}C(\pi)\le\frac{\sqrt2+\sqrt6}{2}\,\mathrm{OPT}.$$
--   2. **Zero-setup guarantee.** When $K=0$, $\inf_{\pi\in\Pi_{\rm S}}C(\pi)\le\sqrt2\,\mathrm{OPT}$ on every demand environment.
--   3. **The algorithm at $K=0$.** For $h,\lambda>0$, with $\mu=\lambda L$ and $a=p\lambda/h$, let $S^\star$ be any integer minimizing $L_j(a)$. On every demand environment a policy selected by the rule of Corollary 1 exists, and every such policy is an integer base-stock policy (possibly level $0$) whose cost equals $\inf_{\pi\in\Pi_{\rm S}}C(\pi)$.
--   4. **Tightness.** In normalized parameters,
--   $$\sup_{\mu,a>0}\frac{U_\mu(a)}{\mathrm{OPT}_0(\mu,a)}=\sqrt2.$$
--   5. **The ratio is well defined.** For $\mu,a>0$, $\mathrm{OPT}_0(\mu,a)\ge\mathcal L_\mu(a)\ge\min\{1,a\}>0$.
--
--   The constant $(\sqrt2+\sqrt6)/2=1.93185\ldots$ is the root $R>1$ of $R^2=\sqrt2R+1$. The theorem gives the first constant-factor guarantee valid at every finite parameter vector for this model with positive lead time and arbitrary fixed ordering costs.
--
--   **Formalization Note** Policy costs are evaluated on an arbitrary demand environment $S$ (a probability space with a filtration carrying the Poisson demand count), while $\mathrm{OPT}$ is the infimum over all environments and all admissible policies on them. Costs and $\mathrm{OPT}$ are in $[0,\infty]$, so the inequalities are meaningful even when $\mathrm{OPT}=0$ (for instance $\lambda=0$, $p=0$ or $h=0$), where the infima need not be attained. The ratio in item 4 is division in $[0,\infty]$ of $U_\mu(a)$ by $\mathrm{OPT}_0(\mu,a)$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Theorem 1, eqs. (5)-(7) (p. 8).

import Definitions.Def_LostSalesRQ_model
import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem main_theorem :
    (∀ lam L h p K : ℝ, 0 ≤ lam → 0 ≤ L → 0 ≤ h → 0 ≤ p → 0 ≤ K →
      ∀ S : DemandSpace lam,
        rQFamilyCost S L h p K ≤
          ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) * OPT lam L h p K) ∧
    (∀ lam L h p : ℝ, 0 ≤ lam → 0 ≤ L → 0 ≤ h → 0 ≤ p →
      ∀ S : DemandSpace lam,
        baseStockFamilyCost S L h p ≤ ENNReal.ofReal (Real.sqrt 2) * OPT lam L h p 0) ∧
    (∀ lam L h p : ℝ, 0 < lam → 0 ≤ L → 0 < h → 0 ≤ p →
      ∀ S : DemandSpace lam, ∀ Sstar : ℕ,
        (∀ j : ℕ, baseStockCost (lam * L) (p * lam / h) Sstar ≤
          baseStockCost (lam * L) (p * lam / h) j) →
        (∃ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) 0 Sstar π) ∧
        ∀ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) 0 Sstar π →
          π ∈ baseStockFamily S L ∧ π.avgCost L h p 0 = baseStockFamilyCost S L h p) ∧
    (⨆ (μ : ℝ) (a : ℝ) (_ : 0 < μ ∧ 0 < a),
        ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0) = ENNReal.ofReal (Real.sqrt 2) ∧
    (∀ μ a : ℝ, 0 < μ → 0 < a →
      ENNReal.ofReal (lowerCurve μ a) ≤ OPTk μ a 0 ∧ min 1 a ≤ lowerCurve μ a ∧
        0 < min 1 a) := by sorry

end LostSalesRQ
