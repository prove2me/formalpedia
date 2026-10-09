-- Prove2me | Theorems.Thm_OnlineCRS_Matching_exponential_bound
-- name    : OnlineCRS.Matching.exponential_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:23.779291+00:00
-- url     : https://prove2.me/theorems/ebbda813-5887-4de6-b279-28b3ffdf48bf
-- title:
--   Proof of Theorem 2.7, p. 13 — e^{t}(e^{t} − 1)/t ≥ 1 for t > 0
-- statement:
--   For every real $t>0$,
--
--   $$\frac{e^{t}\,(e^{t}-1)}{t}\ \ge\ 1.$$
--
--   With $t=x_{g'}$ this is the last inequality of the chain in the proof of Theorem 2.7: $\frac{1-e^{-x_{g'}}}{x_{g'}}e^{-2(b-x_{g'})}=\frac{e^{x_{g'}}(e^{x_{g'}}-1)}{x_{g'}}e^{-2b}\ge e^{-2b}$.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, p. 13, last inequality of the display

import Mathlib

namespace OnlineCRS.Matching

/-- Proof of Theorem 2.7, p. 13: the last inequality in the displayed chain. -/
theorem exponential_bound (t : ℝ) (ht : 0 < t) :
    1 ≤ Real.exp t * (Real.exp t - 1) / t := by sorry

end OnlineCRS.Matching
