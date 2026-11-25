-- Prove2me | Theorems.Thm_Kyprianou_Ch04_WHRatioLimitRegularNonzeroExponent
-- name    : Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T19:27:09.405968+00:00
-- url     : https://prove2.me/theorems/b530202c-fe3e-4aad-9215-f6a30d39e93e
-- title:
--   Regular small-discount Wiener–Hopf quotient limit away from psi(beta)=0
-- statement:
--   With q tending to zero, the positive-root sequence r tending to zero and q/r tending to m, the WH ratio (q/r)(r-beta)/(q-psi(beta)) tends to m beta/psi(beta) whenever psi(beta) is nonzero. The removable singular case is deliberately separate.
-- source:
--   Kyprianou (2006), Corollary 4.9, small-discount Wiener–Hopf transform limit.

import Mathlib
open Filter
set_option autoImplicit false

theorem Kyprianou.Ch04.WHRatioLimitRegularNonzeroExponent
    (q r : ℕ → ℝ) (beta m psiBeta : ℝ)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (nhds 0))
    (hr0 : Tendsto r atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (nhds (m * beta / psiBeta)) := by
  sorry
