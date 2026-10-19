-- Prove2me | Theorems.Thm_MetricCodes_Johnson_finite_binaryCodeNumber_bound_of_projection_gram
-- name    : MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/f01aae74-caaf-44f3-b629-28045d5b0067
-- title:
--   MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

theorem MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) := by sorry
