-- Prove2me | Theorems.Thm_LL_SPLIT_delay_bound18_bjs_lemma10_H_le
-- name    : LL_SPLIT_delay_bound18.bjs_lemma10_H_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T15:32:27.319099+00:00
-- url     : https://prove2.me/theorems/d06b2e65-1109-4740-88f5-4603986b32a9
-- title:
--   Tail integral bound $H(s)\le 0.9607\,s\,h(s)$ for $s\ge 2$
-- statement:
--   For every real $s\ge 2$, $\int_s^\infty h(t-1)\,dt\le 0.9607\,s\,h(s)$. The ratio of the two sides is largest at $s=2$, where it is about $0.96068$.
-- source:
--   M. Bordignon, D. R. Johnston and V. Starichkova, arXiv:2207.09452, Lemma 10

import Mathlib
import Definitions.Def_LL_SPLIT_delay_bound18_hS

open Real Finset Classical MeasureTheory Set

namespace LL_SPLIT_delay_bound18
theorem bjs_lemma10_H_le (s : ℝ) (hs : 2 ≤ s) :
    ∫ t in Ioi s, hS (t - 1) ≤ 0.9607 * s * hS s := by sorry
end LL_SPLIT_delay_bound18
