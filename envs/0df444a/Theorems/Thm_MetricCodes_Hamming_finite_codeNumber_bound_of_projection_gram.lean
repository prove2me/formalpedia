-- Prove2me | Theorems.Thm_MetricCodes_Hamming_finite_codeNumber_bound_of_projection_gram
-- name    : MetricCodes.Hamming.finite_codeNumber_bound_of_projection_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/be6a1b2a-32c5-4beb-9207-54b6240357b9
-- title:
--   MetricCodes.Hamming.finite_codeNumber_bound_of_projection_gram
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

theorem MetricCodes.Hamming.finite_codeNumber_bound_of_projection_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x y : BinaryWord n,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by sorry
