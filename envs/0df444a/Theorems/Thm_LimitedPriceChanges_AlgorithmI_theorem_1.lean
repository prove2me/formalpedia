-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_theorem_1
-- name    : LimitedPriceChanges.AlgorithmI.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:17.497559+00:00
-- url     : https://prove2.me/theorems/c574cc0d-6ff7-4fbe-ae63-e57e40e93998
-- title:
--   Theorem 1, p. 10 — Algorithm-I with m price changes has regret R(T) ≤ K₆T^{1/(m+1)} for T large
-- statement:
--   A firm sells one product over $T$ periods. Each period it sets a price $p_t\in\mathcal P=[p^l,p^h]$ and an order-up-to level $y_t\in\mathcal Y=\{y^l,\dots,y^h\}$ with $y_t\ge x_t$, the carried inventory; demand has pmf $f(\cdot;p_t,z)$ on $\{d^l,\dots,d^h\}$, known up to a scalar parameter $z\in\mathcal Z=[z^l,z^h]$; unmet demand is lost and only the sales $\min\{d_t,y_t\}$ are observed. The single-period expected profit is $G(p,y,z)$ of (4) and the clairvoyant value is $G^*(z)=\max_{(p,y)\in\mathcal P\times\mathcal Y}G(p,y,z)$.
--
--   Assume the standing hypotheses of §2–§3 at the true parameter $z$: $\mathbb E[D(p,z)]>0$ on $\mathcal P$, Assumption A, every optimal order-up-to level exceeds $d^l$, the family is well-separated (Definition 1), and Assumption 1. Run Algorithm-I with $m\ge1$ price changes, inputs $\hat p_1\in\mathcal P$, $\hat y_1\in\mathcal Y$, $\Delta\ge1$, and any maximum-likelihood and plug-in selections for Steps 2 and 3.
--
--   Then there is a constant $K_6>0$ such that, for every large enough $T$, the regret $R(T)=\sum_{t=1}^T\mathbb E[G^*(z)-G(p_t,y_t,z)]$ of Algorithm-I satisfies
--   $$
--   R(T)\le K_6\,T^{\frac1{m+1}} .
--   $$
--
--   With a fixed budget of $m$ price changes, the regret grows only as $T^{1/(m+1)}$ despite censored demand; Theorem 2 of the paper shows this rate cannot be improved in general.
--
--   **Formalization Note** The expectation is a sum over demand paths $d\in\mathbb N^T$ weighted by $\prod_tf(d_t;p_t,z)$, the law of the path under the algorithm, in $[0,\infty]$; each summand $G^*(z)-G(p_t,y_t,z)$ is nonnegative. Step 3's arg max is read through the price selection $p^*$ of Assumption A(iii) ($\hat p=p^*_{\hat y}(\hat z)$, $\hat y$ any maximizer of $y\mapsto G(p^*_y(\hat z),y,\hat z)$), and Step 2's MLE is any maximizer of the censored product likelihood. Added hypotheses, disclosed: differentiability of $f$ in $z$ on $\mathcal Z$ and finiteness of the mean demand (both presupposed by the page), and $d^l\le y^l$ (so that Step 1's cases cover $\mathcal Y$). "The optimal order-up-to level is greater than $d^l$" is read for every optimal level. $K_6$ may depend on the model, $z$, the inputs and the selections; "for $T$ large enough" is an explicit threshold $T_0$. $T^{1/(m+1)}$ is a real power.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 10, Theorem 1; proof pp. 24–27

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **Theorem 1** (p. 10). In the well-separated case, under the standing hypotheses of §2–§3
(Assumption A, Definition 1, Assumption 1, every optimal order-up-to level above `dl`), there is
a constant `K₆ > 0` such that, for `T` large enough, the regret of Algorithm-I with `m` price
changes satisfies `R(T) ≤ K₆ T^{1/(m+1)}`. -/
theorem theorem_1 (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K₆ : ℝ, 0 < K₆ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      A.regret z T ≤ ENNReal.ofReal (K₆ * (T : ℝ) ^ ((1 : ℝ) / ((A.m : ℝ) + 1))) := by sorry

end LimitedPriceChanges.AlgorithmI
