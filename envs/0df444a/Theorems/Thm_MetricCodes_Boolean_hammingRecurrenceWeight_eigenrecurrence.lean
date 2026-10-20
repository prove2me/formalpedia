-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingRecurrenceWeight_eigenrecurrence
-- name    : MetricCodes.Boolean.hammingRecurrenceWeight_eigenrecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/850bb2b2-d122-47fe-8c79-7d274ea15936
-- title:
--   MetricCodes.Boolean.hammingRecurrenceWeight_eigenrecurrence
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

theorem MetricCodes.Boolean.hammingRecurrenceWeight_eigenrecurrence
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1))) (lam : ℝ)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (m : Fin (L - k + 1)) :
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      lam * hammingRecurrenceWeight n k L v m := by sorry
