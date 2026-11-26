-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_renewal_algebra
-- name    : Kyprianou.Ch04.cor412_renewal_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:30.526264+00:00
-- url     : https://prove2.me/theorems/c81b001b-9c03-421a-81eb-c602bfd979fa
-- title:
--   Defective descending renewal transform solved by scalar cancellation
-- statement:
--   Defective descending renewal transform solved by scalar cancellation.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_renewal_algebra (m d β ψ W K : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hβ : 0 < β) (hψ : 0 < ψ)
    (hW : W = m * β / ψ) (hrenew : W = m / d + K * W) :
    K = 1 - ψ / (d * β) := by sorry
