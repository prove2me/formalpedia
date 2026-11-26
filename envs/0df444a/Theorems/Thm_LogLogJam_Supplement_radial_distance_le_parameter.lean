-- Prove2me | Theorems.Thm_LogLogJam_Supplement_radial_distance_le_parameter
-- name    : LogLogJam.Supplement.radial_distance_le_parameter
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:14.540803+00:00
-- url     : https://prove2.me/theorems/3ed565ba-8b91-4ed3-8780-62705aa63497
-- title:
--   Squeezing error bounds the equal-angle trace distance
-- statement:
--   For any real squeezing parameters $r,s$, the equal-angle pure-state distance from Eq. (179) satisfies $\sqrt{1-1/\cosh(r-s)}\leq |r-s|$. The estimate is uniform in the initial squeezing.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §8.3.4, Eq. (179)

import Mathlib

namespace LogLogJam.Supplement

theorem radial_distance_le_parameter (r s : ℝ) :
    Real.sqrt (1 - 1 / Real.cosh (r - s)) ≤ |r - s| := by sorry

end LogLogJam.Supplement
