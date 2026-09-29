-- Prove2me | Theorems.Thm_LiuVanRyzin_cutoff_exists_unique
-- name    : LiuVanRyzin.cutoff_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:36:22.767844+00:00
-- url     : https://prove2.me/theorems/15c1145e-a9ea-4c7b-821e-823f7a5c0e07
-- title:
--   Proposition 1 — for every fill rate $q\in[0,1)$ the purchase threshold $v(q)\ge p_1$ exists and is unique
-- statement:
--   Let $u$ be a customer utility (strictly increasing, concave and continuous on $[0,\infty)$, twice differentiable on $(0,\infty)$, $u(0)=0$), let $p_2<p_1$ be the two prices, and let $q\in[0,1)$ be the anticipated period-2 fill rate. A customer with valuation $v$ buys early when $v\ge p_1$ and $u(v-p_1)\ge q\,u(v-p_2)$. Let $v(q)$ be the infimum of the valuations that buy early. Then
--
--   1. $v(q)\ge p_1$;
--   2. every customer with valuation $v>v(q)$ buys in period 1;
--   3. no customer with valuation $v<v(q)$ buys in period 1;
--   4. $v(q)$ is the only number $t\ge p_1$ with properties 2 and 3.
--
--   $$\forall q\in[0,1):\qquad \{v: v>v(q)\}\subseteq\{\text{early buyers}\}\subseteq\{v: v\ge v(q)\},\quad v(q)\ge p_1.$$
--
--   The threshold is the customers' best response to the firm's capacity decision; every later result of the paper is phrased through it.
--
--   **Formalization Note** The threshold is constructed as `sInf` of the buy set, not assumed. The hypotheses on $u$ are §2's standing assumptions (p. 1120), placed on the half-line where customers evaluate $u$; continuity at $0$ is added as described in the definition module.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1120, Proposition 1

import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

/-- Proposition 1 (Liu–van Ryzin 2008, p. 1120). For every fill rate `q ∈ [0, 1)` the threshold
`v(q) ≥ p₁` exists and is unique: valuations above it buy in period 1, valuations below it wait. -/
theorem cutoff_exists_unique (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    p₁ ≤ cutoff u p₁ p₂ q ∧
      (∀ v : ℝ, cutoff u p₁ p₂ q < v → buysEarly u p₁ p₂ q v) ∧
      (∀ v : ℝ, v < cutoff u p₁ p₂ q → ¬ buysEarly u p₁ p₂ q v) ∧
      (∀ t : ℝ, p₁ ≤ t → (∀ v : ℝ, t < v → buysEarly u p₁ p₂ q v) →
        (∀ v : ℝ, v < t → ¬ buysEarly u p₁ p₂ q v) → t = cutoff u p₁ p₂ q) := by sorry

end LiuVanRyzin
