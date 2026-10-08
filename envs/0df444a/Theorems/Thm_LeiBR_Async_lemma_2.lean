-- Prove2me | Theorems.Thm_LeiBR_Async_lemma_2
-- name    : LeiBR.Async.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:23.992658+00:00
-- url     : https://prove2.me/theorems/2cf622ba-14ef-47f5-8d03-5dd1cbee4a83
-- title:
--   Lemma 2 — $zc^z \le Dq^z$ for $0<c<q<1$ and $D \ge 1/\ln((q/c)^e)$
-- statement:
--   Let $0 < c < 1$ and $c < q < 1$, and let
--   $$D \ge \frac{1}{\ln\big((q/c)^e\big)} = \frac{1}{e\,\ln(q/c)} .$$
--   Then for every real $z \ge 0$,
--   $$z\,c^z \le D\,q^z .$$
--
--   The lemma trades a sublinear factor $z$ for a slightly slower geometric rate $q > c$; it converts the bound (41) into the purely geometric bound (42).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 9, Lemma 2

import Mathlib

namespace LeiBR.Async

/-- Lemma 2 (p. 9): for `0 < c < 1`, `c < q < 1` and `D ≥ 1/ln((q/c)^e) = 1/(e·ln(q/c))`,
`z c^z ≤ D q^z` for every real `z ≥ 0`. -/
theorem lemma_2 (c q D z : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) (hz : 0 ≤ z) :
    z * c ^ z ≤ D * q ^ z := by sorry

end LeiBR.Async
