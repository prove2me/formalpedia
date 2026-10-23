-- Prove2me | Theorems.Thm_Muckstadt2005_thm2_infinite_horizon_faithful
-- name    : Muckstadt2005.thm2_infinite_horizon_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:23.084012+00:00
-- url     : https://prove2.me/theorems/b9bfd791-322a-4a0a-a638-a37ca1c37d81
-- title:
--   Theorem 2 for the infinite-horizon value function (lead time one)
-- statement:
--   Consider the periodic-review backorder model of Section 2.1 with lead time one period: i.i.d. period demands with a density $g$ that is positive and continuous on $(0, \infty)$ and has finite mean, unit purchase, holding and backorder costs $c \ge 0$, $h > 0$, $b$, a discount factor $0 < \alpha < 1$ with $b > \frac{1-\alpha}{\alpha}c$, and the expected one-period cost $L(y)$. Let $f_1 = L$ and
--
--   $$f_n(y) = \min_{u \ge 0}\Big\{cu + L(y) + \alpha\int_0^\infty f_{n-1}(y + u - x)\,g(x)\,dx\Big\}, \qquad n \ge 2,$$
--
--   and let $f(y) = \lim_{n \to \infty} f_n(y)$ be the infinite-horizon value function. Then there is a real $s^*$ such that, for every inventory position $y$, the order $u^*(y) = \max\{0, s^* - y\}$ minimizes
--
--   $$cu + L(y) + \alpha\int_0^\infty f(y + u - x)\,g(x)\,dx \quad \text{over all } u \ge 0.$$
--
--   This is Theorem 2 of Muckstadt (2005), p. 18, for its infinite-horizon problem (2.1) with lead time one, i.e. the conjecture the book states but does not prove on p. 21. The existing theorem ServiceParts.BaseStock.order_up_to_optimal proves the finite-horizon form; this statement is about the limit of the $f_n$.
--
--   **Formalization Note** The limit $f$ enters as any function to which the $f_n$ converge pointwise; under the model assumptions the sequence is nondecreasing in $n$ and bounded, so such an $f$ exists and the hypothesis is not vacuous. The index $0$ of the recursion is a placeholder and does not affect the limit.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, doi:10.1007/b138879, p. 18, Theorem 2 (infinite-horizon equation (2.1), p. 16; conjecture for n → ∞, p. 21), lead time τ = 1

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

theorem Muckstadt2005.thm2_infinite_horizon_faithful (M : ServiceParts.BaseStock.Model)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, Tendsto (fun n : ℕ => M.f n y) atTop (𝓝 (f y))) :
    ∃ s : ℝ, ∀ y : ℝ, ∀ u : ℝ, 0 ≤ u →
      M.stageCost f y (max 0 (s - y)) ≤ M.stageCost f y u := by sorry
