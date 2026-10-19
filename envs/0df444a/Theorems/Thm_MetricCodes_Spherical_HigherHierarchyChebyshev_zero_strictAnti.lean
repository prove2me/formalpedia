-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zero_strictAnti
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.zero_strictAnti
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/560a6105-3427-4578-a8d1-5191b37ae96f
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.zero_strictAnti
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.zero_strictAnti {R : ℝ} (hR : 0 < R)
    {N i j : ℕ} (hN : 0 < N) (hj : j ≤ N) (hij : i < j) :
    zero R N j < zero R N i := by sorry
