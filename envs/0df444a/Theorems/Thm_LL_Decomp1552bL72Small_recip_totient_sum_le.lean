-- Prove2me | Theorems.Thm_LL_Decomp1552bL72Small_recip_totient_sum_le
-- name    : LL_Decomp1552bL72Small.recip_totient_sum_le
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-24T15:02:15.426264+00:00
-- url     : https://prove2.me/theorems/371982f3-06f2-4553-ac65-38e155bb86d5
-- title:
--   Reciprocal totient sum below $3\,\{\log D+1\}$
-- statement:
--   For every real number $D\ge 1$, the sum of $1/\varphi(m)$ over the integers $1\le m<\lceil D\rceil$ is at most $3\,\{\log D+1\}$, where $\varphi$ is Euler's totient function and $\log$ is the natural logarithm.
-- source:
--   T. Yamada, Explicit Chen's theorem, arXiv:1511.03409, Section 7, proof of Lemma 7.2, small conductor sum

import Mathlib

open Finset Real
open scoped Classical

namespace LL_Decomp1552bL72Small
theorem recip_totient_sum_le (D : ℝ) (hD : 1 ≤ D) :
    ∑ m ∈ Ico 1 ⌈D⌉₊, (1 / (m.totient : ℝ)) ≤ 3 * (log D + 1) := by sorry
end LL_Decomp1552bL72Small
