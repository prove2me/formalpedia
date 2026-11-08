-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_3
-- name    : KhintchineTwoRegime.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:39.188785+00:00
-- url     : https://prove2.me/theorems/18bdd29f-a35b-4ab8-b017-fd9027f1eabf
-- title:
--   Lemma 3 — finite certificate: $\max\{J(a,b),H(a,b)\}>7423/10000$
-- statement:
--   Put $k=7423/10000$. If
--   $$
--   \frac12\le a\le k,\qquad 0\le b\le a,\qquad a+b\le1,
--   $$
--   then
--   $$
--   \max\{J(a,b),\,H(a,b)\}>k.
--   $$
--   This is a statement about two explicit real functions, certified in the paper by a finite table of rational bounds; it is the core numerical input of Corollary 1.
--
--   Differences from the source: none.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 3, p.6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_J
import Definitions.Def_KhintchineTwoRegime_H

namespace KhintchineTwoRegime

/-- Lemma 3 (A finite coefficient certificate) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.6): put `k = 7423/10000`; if
`1/2 ≤ a ≤ k`, `0 ≤ b ≤ a` and `a + b ≤ 1`, then `max{J(a, b), H(a, b)} > k`. -/
theorem lemma_3 (a b : ℝ) (ha₁ : 1 / 2 ≤ a) (ha₂ : a ≤ 7423 / 10000) (hb₀ : 0 ≤ b) (hba : b ≤ a)
    (hab : a + b ≤ 1) :
    (7423 : ℝ) / 10000 < max (J a b) (H a b) := by sorry

end KhintchineTwoRegime
