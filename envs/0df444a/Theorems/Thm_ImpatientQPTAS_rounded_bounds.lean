-- Prove2me | Theorems.Thm_ImpatientQPTAS_rounded_bounds
-- name    : ImpatientQPTAS.rounded_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:49.555538+00:00
-- url     : https://prove2.me/theorems/0c1da105-381d-4b31-b727-e7f2c57f33b8
-- title:
--   §2.3, p.10 — $p_i\in[p^\downarrow_i,p^\uparrow_i]$, and both are strictly inside $(0,1)$
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$ and let $i$ be an average customer. Then
--   $$
--   0<p^\downarrow_i\le p_i\le p^\uparrow_i<1 .
--   $$
--
--   The outer bounds make the ratios and powers of §§2.3 and 3.3 meaningful.
--
--   Differences from the source:
--   - generalization: p_i ∈ [p↓_i, p↑_i] → in addition 0 < p↓_i and p↑_i < 1; reason: the extra bounds are used implicitly on pp.16–17; the printed claim is the middle of the chain
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.3, p.10

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.3, p.10: "one can easily verify that p_i ∈ [p↓_i, p↑_i]". For an average
customer, moreover, `0 < p↓_i` and `p↑_i < 1`, so the ratios and powers of §§2.3–3.3 are meaningful. -/
theorem rounded_bounds {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) :
    0 < pDown ε (I.p i) ∧ pDown ε (I.p i) ≤ I.p i ∧ I.p i ≤ pUp ε (I.p i) ∧
      pUp ε (I.p i) < 1 := by sorry

end ImpatientQPTAS
