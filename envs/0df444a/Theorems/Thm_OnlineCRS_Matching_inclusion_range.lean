-- Prove2me | Theorems.Thm_OnlineCRS_Matching_inclusion_range
-- name    : OnlineCRS.Matching.inclusion_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:20.036135+00:00
-- url     : https://prove2.me/theorems/f97b91d9-4bea-4d77-9728-c9b6d563b6eb
-- title:
--   Proof of Theorem 2.7, p. 13 — the inclusion probability (1 − e^{−x_g})/x_g lies in [0, 1]
-- statement:
--   For every real $t>0$,
--
--   $$0\le\frac{1-e^{-t}}{t}\le1.$$
--
--   In the proof of Theorem 2.7 every edge $g$ enters the random set $K$ of potential edges with probability $(1-e^{-x_g})/x_g$; this inequality shows that this number is a probability.
--
--   **Formalization Note** The statement is for $t>0$, where the paper's ratio is defined; at $x_g=0$ the construction uses the limit value $1$.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, p. 13, first paragraph (parenthetical remark)

import Mathlib

namespace OnlineCRS.Matching

/-- Proof of Theorem 2.7, p. 13, first paragraph: for `x_g > 0` the probability `(1 − e^{−x_g})/x_g`
with which an edge is put into `K` lies in `[0, 1]`. -/
theorem inclusion_range (t : ℝ) (ht : 0 < t) :
    0 ≤ (1 - Real.exp (-t)) / t ∧ (1 - Real.exp (-t)) / t ≤ 1 := by sorry

end OnlineCRS.Matching
