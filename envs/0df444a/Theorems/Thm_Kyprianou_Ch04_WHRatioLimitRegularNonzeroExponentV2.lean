-- Prove2me | Theorems.Thm_Kyprianou_Ch04_WHRatioLimitRegularNonzeroExponentV2
-- name    : Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponentV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:34:03.224353+00:00
-- url     : https://prove2.me/theorems/ab3b7e84-8b34-4c97-80e7-0937f885c9d2
-- title:
--   Regular small-discount Wiener–Hopf quotient limit away from psi(beta)=0
-- statement:
--   With q tending to zero, the positive-root sequence r tending to zero and q/r tending to m, the WH ratio (q/r)(r-beta)/(q-psi(beta)) tends to m beta/psi(beta) whenever psi(beta) is nonzero. The removable singular case is deliberately separate.
-- source:
--   Kyprianou (2006), Corollary 4.9, small-discount Wiener–Hopf transform limit.

import Mathlib
open Filter
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponentV2
    (q r : ℕ → ℝ) (beta m psiBeta : ℝ)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (𝓝 0))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (𝓝 m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (𝓝 (m * beta / psiBeta)) := by
  sorry
