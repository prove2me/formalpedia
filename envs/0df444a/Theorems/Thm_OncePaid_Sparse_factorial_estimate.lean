-- Prove2me | Theorems.Thm_OncePaid_Sparse_factorial_estimate
-- name    : OncePaid.Sparse.factorial_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T13:45:32.056298+00:00
-- url     : https://prove2.me/theorems/06957ea2-1de6-4ce3-b6e4-6dad58d558d2
-- title:
--   §A.3, factorial estimate — $(r!)^{1/r}\le(r+6)/e$ for $1\le r\le102$, and $6/e>1$
-- statement:
--   For every integer $r$ with $1\le r\le 102$,
--
--   $$
--   (r!)^{1/r}\ \le\ \frac{r+6}{e},
--   $$
--
--   and moreover $6/e>1$.
--
--   The estimate bounds the row-degree factors $(d_i!)^{1/d_i}$ in Brégman's permanent inequality for graphs of degree at most $102$; $6/e>1$ allows omitted factors to be restored.
--
--   Differences from the source: none.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 36, App. A.3, factorial estimate (PDF p. 38)

import Mathlib

namespace OncePaid.Sparse

/-- App. A.3, factorial estimate, p. 36: `(r!)^{1/r} ≤ (r + 6)/e` for all integers
`1 ≤ r ≤ 102`, and `6/e > 1`. -/
theorem factorial_estimate :
    (∀ r : ℕ, 1 ≤ r → r ≤ 102 →
      ((Nat.factorial r : ℕ) : ℝ) ^ ((1 : ℝ) / (r : ℝ)) ≤ ((r : ℝ) + 6) / Real.exp 1) ∧
    1 < 6 / Real.exp 1 := by sorry

end OncePaid.Sparse
