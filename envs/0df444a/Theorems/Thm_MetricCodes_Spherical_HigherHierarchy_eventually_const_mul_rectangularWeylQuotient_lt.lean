-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_const_mul_rectangularWeylQuotient_lt
-- name    : MetricCodes.Spherical.HigherHierarchy.eventually_const_mul_rectangularWeylQuotient_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/b587da6b-08e7-4e4a-a02b-d50b65d72a78
-- title:
--   MetricCodes.Spherical.HigherHierarchy.eventually_const_mul_rectangularWeylQuotient_lt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation

theorem MetricCodes.Spherical.HigherHierarchy.eventually_const_mul_rectangularWeylQuotient_lt
    {r m : ℕ} {R K : ℝ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last (r + 1)))
    (hR : Phi a b < R) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K *
          (RectangularVertices.dimensionSum (m := m) a n /
            Weyl.dimension (n - 1)
              (Weyl.flooredWeight b n)) <
        (2 : ℝ) ^ (R * (n : ℝ)) := by sorry
