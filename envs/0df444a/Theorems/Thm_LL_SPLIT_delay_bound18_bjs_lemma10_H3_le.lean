-- Prove2me | Theorems.Thm_LL_SPLIT_delay_bound18_bjs_lemma10_H3_le
-- name    : LL_SPLIT_delay_bound18.bjs_lemma10_H3_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T15:20:10.514512+00:00
-- url     : https://prove2.me/theorems/25ee166c-56e7-405f-9d24-745f4a0ec415
-- title:
--   Bound $H(3)\le 0.9214\,s\,h(s)$ for $1\le s\le 3$
-- statement:
--   For every real $s$ with $1\le s\le 3$, $\int_3^\infty h(t-1)\,dt\le 0.9214\,s\,h(s)$. The tightest case is $s=1$, with absolute margin about $4.6\cdot10^{-6}$.
-- source:
--   M. Bordignon, D. R. Johnston and V. Starichkova, arXiv:2207.09452, Lemma 10

import Mathlib
import Definitions.Def_LL_SPLIT_delay_bound18_hS

open Real Finset Classical MeasureTheory Set

namespace LL_SPLIT_delay_bound18
theorem bjs_lemma10_H3_le (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    ∫ t in Ioi (3 : ℝ), hS (t - 1) ≤ 0.9214 * s * hS s := by sorry
end LL_SPLIT_delay_bound18
