-- Prove2me | Theorems.Thm_Grunbaum2003_repaired_ray_query_budget_bound
-- name    : Grunbaum2003.repaired_ray_query_budget_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:21.476718+00:00
-- url     : https://prove2.me/theorems/8e3336c6-127f-43fd-b79e-e1c8ebeafe8b
-- title:
--   Gritzmann–Klee–Westwater ray-shooting query budget summation and bound
-- statement:
--   This lemma proves the summation identity and global query-budget inequality for the Gritzmann–Klee–Westwater ray-oracle reconstruction bound in dimensions $d \ge 2$ when the facet count $m = f_{d-1}(P)$ satisfies $m \ge d + 1$.
--
--   Let $d, m, f_0 \in \mathbb{N}$ satisfy $d \ge 2$ and $m \ge d + 1$. Then:
--   1. **Planar detector summation (`sum_twice_remaining_add_three`):** Summing the two-charge planar secant-detector cost $2(m - k) + 3$ over $m$ facet-discovery stages ($u = m - k$ unknown facets remaining at stage $k \in \{0, \dots, m - 1\}$) gives
--      $$
--      \sum_{k=0}^{m-1} \bigl(2(m - k) + 3\bigr) = m^2 + 4m.
--      $$
--   2. **Global query budget (`corrected_discovery_budget_fits`):** Accounting for $f_0$ vertex-verification queries, $d + 1$ initial inner-simplex queries, and $1 + (d - 1)\bigl(2(m - k) + 3\bigr)$ queries at stage $k$, the total query count satisfies
--      $$
--      f_0 + (d + 1) + \sum_{k=0}^{m-1} \Bigl(1 + (d - 1)\bigl(2(m - k) + 3\bigr)\Bigr) \le f_0 + (d - 1)m^2 + (5d - 4)m.
--      $$
--
--   **Formalization Note** Because $(5d - 4)m - \bigl(m + 4(d - 1)m\bigr) = (d - 1)m \ge m \ge d + 1$ for $d \ge 2$ and $m \ge d + 1$, the linear coefficient $5d - 4$ absorbs both the $3$-query per-call detector overhead and the $d + 1$ initial simplex queries while preserving the leading quadratic coefficient $(d - 1)m^2$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem repaired_ray_query_budget_bound (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m := by sorry

end Grunbaum2003
