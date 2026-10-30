-- Prove2me | Theorems.Thm_JuschenkoMonod_abs_B_le_four_mul_wobblingNorm_sq
-- name    : JuschenkoMonod.abs_B_le_four_mul_wobblingNorm_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:23:10.467378+00:00
-- url     : https://prove2.me/theorems/b889aee5-e30f-4aca-971a-8bc9d7463429
-- title:
--   Lemma 2.7 — |B(u)| ≤ 4|g|_w² for all u ≥ 0
-- statement:
--   Let $g \in W(\mathbf Z)$. Put $b_0 = |g(0)|$ and $b_j = \big(|g(j)| - |j|\big) + \big(|g(-j)| - |-j|\big)$ for integers $j > 0$, and $B(t) = \sum_{0 \le j \le t} b_j$, the sum over integers $j$. Then $|B(u)| \le 4|g|_{\rm w}^2$ for every real $u \ge 0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 781, Lemma 2.7

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem abs_B_le_four_mul_wobblingNorm_sq (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ)
    (u : ℝ) (hu : 0 ≤ u) : |B g u| ≤ 4 * wobblingNorm g ^ 2 := by
  sorry

end JuschenkoMonod
