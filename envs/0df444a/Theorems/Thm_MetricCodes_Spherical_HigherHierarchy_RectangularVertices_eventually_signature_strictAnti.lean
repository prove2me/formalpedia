-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_signature_strictAnti
-- name    : MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_signature_strictAnti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/7c4074f1-9749-458e-a896-bf975df93b95
-- title:
--   MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_signature_strictAnti
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

theorem MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_signature_strictAnti {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    ∀ᶠ n : ℕ in atTop, StrictAnti (signature a n (v n)) := by sorry
