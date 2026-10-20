-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_log_stabilizerDimension_floor_current_div_log_two
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_log_stabilizerDimension_floor_current_div_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/4bc9a0a6-7790-46e0-b58e-ca27fedf57fd
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_log_stabilizerDimension_floor_current_div_log_two
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
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_log_stabilizerDimension_floor_current_div_log_two
    {r : ℕ} (b : Fin (r + 1) → ℝ)
    (hb : ∀ i, 0 < b i) (hanti : StrictAnti b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Weyl.dimension (n - 1) (Weyl.flooredWeight b n)) /
          (n : ℝ)) / Real.log 2)
      atTop (nhds (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (b i))) := by sorry
