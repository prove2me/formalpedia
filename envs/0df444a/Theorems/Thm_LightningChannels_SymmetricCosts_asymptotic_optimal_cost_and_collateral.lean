-- Prove2me | Theorems.Thm_LightningChannels_SymmetricCosts_asymptotic_optimal_cost_and_collateral
-- name    : LightningChannels.SymmetricCosts.asymptotic_optimal_cost_and_collateral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:26.804873+00:00
-- url     : https://prove2.me/theorems/7ca02f11-775b-477c-b45f-e7364237a49f
-- title:
--   Theorem 3(ii), (8): attained optimal cost and equal collateral asymptotics
-- statement:
--   Fix arbitrary $B>0$ and $\lambda>0$. Let $F_r(x,y)=c^{x,y}(\lambda,\lambda)$ be the exact analytic bidirectional cost (3) on all positive real balance pairs. There exists a real function $m$ such that for every $r>0$ the pair $(m(r),m(r))$ is positive and attains the global minimum of $F_r$. Put $q(r)=(2B\lambda/r)^{1/3}$. There exist constants $K_{\rm cost}>0$, $K_{\rm size}>0$ and $\delta>0$ such that every $0<r<\delta$ satisfies
--
--   $$\left|F_r(m(r),m(r))-\left(3q(r)-\frac B6\right)\right|
--   \le K_{\rm cost}\,r^{1/3},\qquad
--   |m(r)-q(r)|\le K_{\rm size}\,r^{1/3}.$$
--
--   Thus the minimum and its equal attaining balances satisfy both conclusions of Theorem 3(ii):
--
--   $$c^{\rm opt}(\lambda,\lambda)=3(2B\lambda/r)^{1/3}-B/6+O(r^{1/3}),
--   \qquad l_1^*(r)=l_2^*(r)=(2B\lambda/r)^{1/3}+O(r^{1/3}).$$
--
--   The constants may depend on the fixed reset cost and payment rate, but not on $r$. Attainment holds for every positive $r$; the error estimates hold for all sufficiently small positive $r$. The statement includes the absolute collateral error, rather than only a relative limit.
--
--   Differences from the source:
--   - reading: channel sizes in the unit-payment model → all positive real sizes in the exact analytic cost; reason: the source differentiates the closed-form objective on printed pp. 10–11 / PDF pp. 11–12 and explicitly uses a real solution on printed p. 12 / PDF p. 13; no fractional-barrier stochastic claim is made
--   - encoding: minimal cost achieved at equal channel sizes → the exact cost evaluated at an existential diagonal global-minimizer selector for every positive discount rate; reason: the source unique-minimum argument supplies the attaining pair for each positive rate; the selector is constructed in the conclusion and its attained value is the minimum
--   - encoding: two absolute O(r^(1/3)) errors as r decreases to zero → positive constants Kcost, Ksize and δ preceding the universal quantifier over 0 < r < δ; reason: these inequalities are equivalent to both right-sided Big-O assertions, allowing dependence on fixed B and λ only
-- source:
--   Guasoni, P.; Huberman, G.; Shikhelman, C., Lightning Network Economics: Channels, Management Science, Articles in Advance, published online November 6, 2023, https://doi.org/10.1287/mnsc.2022.01664, Theorem 3(ii), equation (8) and the following optimal-size sentence, printed p. 7 / PDF p. 8; Proof of Theorem 3(ii), printed p. 12 / PDF p. 13; attainment: Proof of Theorem 2(ii), printed p. 11 / PDF p. 12.

import Definitions.Def_LightningChannels_SymmetricCosts_IsGlobalMin

set_option autoImplicit false

namespace LightningChannels.SymmetricCosts

/-- Theorem 3(ii), (8) and its optimal-size clause, printed p. 7 / PDF p. 8;
proof printed p. 12 / PDF p. 13. Both absolute errors are O(r^(1/3)).
The selector attains the exact global minimum over all positive real pairs for every r > 0.
Fixed positive B and rate precede the selector and constants; no estimate is a hypothesis. -/
theorem asymptotic_optimal_cost_and_collateral (B rate : ℝ)
    (hB : 0 < B) (hRate : 0 < rate) :
    ∃ m : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → IsGlobalMin B rate r (m r) (m r)) ∧
      ∃ Kcost Ksize δ : ℝ, 0 < Kcost ∧ 0 < Ksize ∧ 0 < δ ∧
        ∀ r : ℝ, 0 < r → r < δ →
          |LNChannels.RateBounds.biCost rate rate r B (m r) (m r) -
            (3 * (2 * B * rate / r) ^ (1 / 3 : ℝ) - B / 6)| ≤
              Kcost * r ^ (1 / 3 : ℝ) ∧
          |m r - (2 * B * rate / r) ^ (1 / 3 : ℝ)| ≤
              Ksize * r ^ (1 / 3 : ℝ) := by sorry

end LightningChannels.SymmetricCosts
