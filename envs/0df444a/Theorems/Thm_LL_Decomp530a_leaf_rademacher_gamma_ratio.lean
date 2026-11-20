-- Prove2me | Theorems.Thm_LL_Decomp530a_leaf_rademacher_gamma_ratio
-- name    : LL_Decomp530a.leaf_rademacher_gamma_ratio
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-17T15:38:22.220225+00:00
-- url     : https://prove2.me/theorems/6f893b38-f3e8-4bf5-84b2-04849daf4940
-- title:
--   Rademacher's Gamma quotient estimate
-- statement:
--   For every real $Q\ge0$ and every complex $s$ with $-1/2\le\operatorname{Re}s\le1/2$, one has $\left|\Gamma\big(\tfrac{Q}{2}+\tfrac{1-s}{2}\big)\big/\Gamma\big(\tfrac{Q}{2}+\tfrac{s}{2}\big)\right|\le\big(|Q+1+s|/2\big)^{1/2-\operatorname{Re}s}$, where the right side is a real power of a nonnegative real number.
-- source:
--   Rademacher 1959, Math. Z. 72, p. 197, Lemma 1, display 5.1; input to Baker, Harman and Pintz 1997, Lemma 8.

import Mathlib

open Classical Complex Set Filter ZMod
open scoped Topology

namespace LL_Decomp530a
theorem leaf_rademacher_gamma_ratio :
    ∀ Q : ℝ, 0 ≤ Q → ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re) := by sorry
end LL_Decomp530a
