-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_prop_2_concurrent_threshold
-- name    : InfoSharing.Diseconomy.prop_2_concurrent_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:23:17.894492+00:00
-- url     : https://prove2.me/theorems/9dfa6737-5536-45f0-8385-a34f9b5beefb
-- title:
--   Proposition 2 — the concurrent threshold $c_d^C$
-- statement:
--   For every $\phi > 0$ there is a threshold $c_d^C$, depending only on $\phi$, with the following property. For every signal model, every $a$, $b > 0$, $c_d > 0$, and every pricing-equilibrium family, the set $N^C$ of numbers of informed manufacturers attained by concurrent outcomes satisfies
--
--   $$N^C = \{0\} \text{ if } 0 < c_d < c_d^C,\qquad 2 \in N^C \text{ if } c_d^C \le c_d,\qquad N^C = \{2\} \text{ if } c_d^C < c_d.$$
--
--   Under concurrent contracting the retailer sells information to both manufacturers or to none, depending on the size of the production diseconomy.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$. The paper writes $n_d^C = 2$ on $[c_d^C, \infty)$; at $c_d = c_d^C$ the retailer is indifferent between $n = 0$ and $n = 2$, so there the statement is that $n = 2$ is attained.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, Proposition 2

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Diseconomy_IsConcurrentOutcome
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

universe u

/-- Proposition 2, p. 253: there exists `c_d^C`, depending only on `φ`, such that under
concurrent information contracting `n_d^C = 0` if `0 < c_d < c_d^C` and `n_d^C = 2` if
`c_d^C ≤ c_d`. At the threshold the retailer is indifferent, so the statement there is that
`2` is attained; above it every outcome has `n = 2`. -/
theorem prop_2_concurrent_threshold :
    ∀ φ : ℝ, 0 < φ → ∃ cC : ℝ,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ) (a b c σ β : ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      IsSignalModel μ θ Y σ β → 0 < b → 0 < c → IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      (c < cC → ConcOptN P = {0}) ∧
      (cC ≤ c → 2 ∈ ConcOptN P) ∧
      (cC < c → ConcOptN P = {2}) := by sorry

end InfoSharing.Diseconomy
