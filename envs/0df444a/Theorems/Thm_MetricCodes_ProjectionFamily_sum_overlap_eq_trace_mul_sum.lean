-- Prove2me | Theorems.Thm_MetricCodes_ProjectionFamily_sum_overlap_eq_trace_mul_sum
-- name    : MetricCodes.ProjectionFamily.sum_overlap_eq_trace_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/98bc09a1-7e6e-42f5-ab83-f7e26ed089f8
-- title:
--   MetricCodes.ProjectionFamily.sum_overlap_eq_trace_mul_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.ProjectionFamily
variable {X : Type*} {D d : ℕ}

theorem MetricCodes.ProjectionFamily.sum_overlap_eq_trace_mul_sum (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) =
      Matrix.trace
        ((∑ x ∈ C, P.projection x) *
          (∑ y ∈ C, P.projection y)) := by sorry
