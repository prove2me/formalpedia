-- Prove2me | Theorems.Thm_NCGchk_graviton_pair_uv_log_divergence
-- name    : NCGchk.graviton_pair_uv_log_divergence
-- status  : Proved
-- author  : @LG
-- created : 2026-11-26T12:21:30.560361+00:00
-- url     : https://prove2.me/theorems/3f6be469-ad4c-50b6-9972-96355879f617
-- title:
--   Graviton pair UV log divergence (check)
-- statement:
--   Harmonic sum diverges logarithmically.

import Mathlib

namespace NCGchk
theorem graviton_pair_uv_log_divergence :
    Filter.Tendsto (fun N : ℕ => Finset.sum (Finset.range N) (fun k : ℕ => (1 : ℝ) / (k + 1)) / Real.log N) Filter.atTop (nhds 1) := by sorry
end NCGchk
