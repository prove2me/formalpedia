-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceHighFrequency
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffDifferenceHighFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:55:25.014907+00:00
-- url     : https://prove2.me/theorems/e83b547a-4075-415e-8b38-9d62ea113b89
-- title:
--   High-frequency compensation cutoff difference supported on [1,z)
-- statement:
--   If z≥1, the difference between the cutoffs 1_(u<z) and 1_(u<1), divided by u, is exactly the inverse function supported on 1≤u<z. This pointwise identity holds for all real u including u=0, and isolates the positive interval producing the alpha-one stable logarithmic imaginary phase.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffDifferenceHighFrequency
    (z u : ℝ) (hz : 1 ≤ z) :
    ((if u < z then (1 : ℝ) else 0) -
      (if u < 1 then (1 : ℝ) else 0)) / u =
        (Set.Ico (1 : ℝ) z).indicator (fun x : ℝ => x⁻¹) u := by
  sorry
