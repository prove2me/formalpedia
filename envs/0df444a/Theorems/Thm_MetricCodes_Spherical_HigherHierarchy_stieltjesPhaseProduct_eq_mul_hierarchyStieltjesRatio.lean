-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
-- name    : MetricCodes.Spherical.HigherHierarchy.stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/f345c1e8-dee6-4cea-b79b-433751e6e16f
-- title:
--   MetricCodes.Spherical.HigherHierarchy.stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
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
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
    {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) :
    stieltjesPhaseProduct a b t =
      t * hierarchyStieltjesRatio a b t := by sorry
