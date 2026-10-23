-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_fact_2
-- name    : MonopolyDemandUncertainty.SBSMP.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:35.039998+00:00
-- url     : https://prove2.me/theorems/db36a8e3-a216-4e0e-ba52-394e83e3661b
-- title:
--   Fact 2, p. 5 (PDF 6) — (5) on [v_, v̄), and a root of p = −D1(p)/D1′(p) lies below a root of p = −D2(p)/D2′(p)
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1, 2 and 3.
--
--   1. For every $v^* \in [\underline v, \bar v)$,
--   $$\frac{D_2(v^*)}{-D_2'(v^*)} > \frac{D_1(v^*)}{-D_1'(v^*)}. \tag{5}$$
--   2. If $p_1 \in V$ solves $p_1 = -D_1(p_1)/D_1'(p_1)$ and $p_2 \in V$ solves $p_2 = -D_2(p_2)/D_2'(p_2)$, then $p_1 < p_2$.
--
--   Fact 2 says that the high state has a larger inverse hazard rate everywhere, so the monopoly price of the low state is strictly below that of the high state.
--
--   **Formalization Note** The page asserts (5) for all $v^* \in V$; at $v^* = \bar v$ both sides are $0$ because $D_i(\bar v)=0$, so (5) is posed on $[\underline v,\bar v)$. Part 2 is stated for roots of the first-order conditions, as printed.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 5, Fact 2, (5) (proof p. 8, §A.3)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Fact 2, p. 5 (PDF 6), proof p. 8 (PDF 9). (a) Inequality (5), `D₂(v)/(-D₂'(v)) > D₁(v)/(-D₁'(v))`,
for `v ∈ [v_, v̄)` (at `v = v̄` both sides are `0`). (b) A root `p₁ ∈ V` of `p = -D₁(p)/D₁'(p)` is
strictly below a root `p₂ ∈ V` of `p = -D₂(p)/D₂'(p)`. Paper's states 1, 2 = indices `0`, `1`. -/
theorem fact_2 (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) :
    (∀ v, E.vlo ≤ v → v < E.vhi → E.D 0 v / E.dens 0 v < E.D 1 v / E.dens 1 v) ∧
      ∀ p₁ ∈ E.V, ∀ p₂ ∈ E.V, p₁ = -(E.D 0 p₁ / deriv (E.D 0) p₁) →
        p₂ = -(E.D 1 p₂ / deriv (E.D 1) p₂) → p₁ < p₂ := by sorry
end MonopolyDemandUncertainty.SBSMP
