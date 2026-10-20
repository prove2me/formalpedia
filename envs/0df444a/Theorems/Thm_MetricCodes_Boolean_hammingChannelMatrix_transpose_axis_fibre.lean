-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingChannelMatrix_transpose_axis_fibre
-- name    : MetricCodes.Boolean.hammingChannelMatrix_transpose_axis_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/a869526d-d34f-4e60-a0fe-42f3332cb937
-- title:
--   MetricCodes.Boolean.hammingChannelMatrix_transpose_axis_fibre
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}

theorem MetricCodes.Boolean.hammingChannelMatrix_transpose_axis_fibre
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingFibreMatrix n k L hk v x := by sorry
