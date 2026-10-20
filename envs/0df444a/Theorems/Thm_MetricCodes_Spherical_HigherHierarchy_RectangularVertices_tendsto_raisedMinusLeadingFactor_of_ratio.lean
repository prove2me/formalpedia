-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_raisedMinusLeadingFactor_of_ratio
-- name    : MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_raisedMinusLeadingFactor_of_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/23cffeab-fc88-4050-ad2e-1e310522e8eb
-- title:
--   MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_raisedMinusLeadingFactor_of_ratio
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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_raisedMinusLeadingFactor_of_ratio {r : ℕ}
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) (ha : 0 ≤ a i)
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i + 1 - wallShift n r) /
          (2 * (ambientShift n (lam n) i + 1)))
      atTop (𝓝 (a i / (2 * a i + 1))) := by sorry
