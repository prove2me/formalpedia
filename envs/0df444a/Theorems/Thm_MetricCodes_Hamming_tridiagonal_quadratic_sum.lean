-- Prove2me | Theorems.Thm_MetricCodes_Hamming_tridiagonal_quadratic_sum
-- name    : MetricCodes.Hamming.tridiagonal_quadratic_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:21.918845+00:00
-- url     : https://prove2.me/theorems/5d0548c3-7f53-440f-9dac-08f689580eb2
-- title:
--   MetricCodes.Hamming.tridiagonal_quadratic_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming

theorem MetricCodes.Hamming.tridiagonal_quadratic_sum
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by sorry
