-- Prove2me | Theorems.Thm_MetricCodes_Hamming_finite_bound
-- name    : MetricCodes.Hamming.finite_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/3f2bda07-8df5-443b-85d2-29dfee42f3a3
-- title:
--   MetricCodes.Hamming.finite_bound
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

theorem MetricCodes.Hamming.finite_bound {n k L d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hkL : k < L) (hLn : L + k ≤ n)
    (hgap : threshold n d < topEigenvalue n k L) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by sorry
