-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingProjectionGramFeature_inner
-- name    : MetricCodes.Boolean.hammingProjectionGramFeature_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/6b7e50d7-9c37-4e6a-befb-961755fbd640
-- title:
--   MetricCodes.Boolean.hammingProjectionGramFeature_inner
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

theorem MetricCodes.Boolean.hammingProjectionGramFeature_inner
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x y : BinaryWord n) :
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y := by sorry
