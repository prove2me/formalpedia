-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_10
-- name    : IntervalExplore.KT1.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:29.255312+00:00
-- url     : https://prove2.me/theorems/04c3f8f2-189b-4084-bc01-d8877c6149a5
-- title:
--   Lemma 10 — a uniform logarithm and power inequality
-- statement:
--   For every real number $x>0$ and every natural number $n\ge3$,
--   $$
--   \ln n<x n^{1/(2x)}.
--   $$
--   This uniform numerical inequality is the supplementary estimate used in Lemma 6. The logarithm is natural, the exponent is real, and the strict inequality is retained.
--
--   Differences from the source: none.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 10, Appendix A, p.18 (PDF p.19)

import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 10, Appendix A, p.18 (PDF p.19). Natural logarithm and real exponent. -/
theorem lemma_10 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 3 ≤ n) :
    Real.log n < x * (n : ℝ) ^ (1 / (2 * x)) := by sorry

end IntervalExplore.KT1
