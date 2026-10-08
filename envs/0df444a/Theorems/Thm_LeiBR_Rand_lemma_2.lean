-- Prove2me | Theorems.Thm_LeiBR_Rand_lemma_2
-- name    : LeiBR.Rand.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:26.32428+00:00
-- url     : https://prove2.me/theorems/83f66575-4858-46a8-98b7-b77ad2b64861
-- title:
--   Lemma 2 — $z c^z \le D q^z$ for $0 < c < q < 1$ and $D \ge 1/(e\ln(q/c))$
-- statement:
--   Let $0 < c < 1$, $c < q < 1$ and
--   $$D \ge \frac{1}{\ln\big((q/c)^e\big)} = \frac{1}{e\,\ln(q/c)}.$$
--   Then for every real $z \ge 0$,
--   $$z\,c^z \le D\,q^z.$$
--
--   The lemma trades the factor $z$ in a sublinear-times-geometric term for a slightly worse geometric rate $q > c$, which turns the recursions of the rate analyses into clean linear rates.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 9, Lemma 2

import Mathlib

namespace LeiBR.Rand

/-- Lemma 2, p. 9: for `0 < c < 1`, `c < q < 1` and `D ≥ 1/ln((q/c)^e) = 1/(e ln(q/c))`,
`z c^z ≤ D q^z` for every real `z ≥ 0`. -/
theorem lemma_2 (c q D : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) (z : ℝ) (hz : 0 ≤ z) :
    z * c ^ z ≤ D * q ^ z := by sorry

end LeiBR.Rand
