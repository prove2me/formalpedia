-- Prove2me | Theorems.Thm_MetricTSP_hk_value_ge_card
-- name    : MetricTSP.hk_value_ge_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:13:28.3198+00:00
-- url     : https://prove2.me/theorems/cd6e346b-931a-40c3-a7fe-8d40507f05eb
-- title:
--   Separated instances have Held--Karp value at least n
-- statement:
--   If every pair of distinct cities is at cost at least $1$, the Held--Karp value is at least the number of cities:
--   $$n \;\le\; \mathrm{hkValue}(c).$$
--
--   Every feasible point of the subtour-elimination relaxation has total mass $\sum_u \sum_v x_{uv} = 2n$ by the degree constraints, and its diagonal vanishes, so the objective $\tfrac12\sum c\,x$ is at least $\tfrac12 \cdot 2n \cdot 1 = n$. (The set of feasible objectives is nonempty because tour incidence vectors are feasible, so the infimum is a genuine one.)
--
--   This is the standard way of bounding LP values away from zero for graph metrics --- in particular it makes the integrality-gap ratio of unweighted families well-defined.
-- source:
--   M. Held, R. M. Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18 (1970) 1138-1162 (the bound is at least n for 1-2 metrics; the degree constraints force total mass 2n).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector

namespace MetricTSP

theorem hk_value_ge_card (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc1 : ∀ u v, u ≠ v → 1 ≤ c u v) : (n : ℝ) ≤ hkValue c := by sorry

end MetricTSP
