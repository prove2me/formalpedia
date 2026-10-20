-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_strict_residual_of_weak_interlacing
-- name    : MetricCodes.Spherical.HigherHierarchy.exists_strict_residual_of_weak_interlacing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/8f3d7f21-7174-483d-ae9e-99e73d0554ae
-- title:
--   MetricCodes.Spherical.HigherHierarchy.exists_strict_residual_of_weak_interlacing
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
open scoped BigOperators

theorem MetricCodes.Spherical.HigherHierarchy.exists_strict_residual_of_weak_interlacing {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) :
    ∃ (j : ℕ) (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ),
      j ≤ r ∧ Interlacing A B ∧ Phi A B = Phi a b ∧
        ∀ t : ℝ, 0 < t →
          (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
              (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i))) =
            (∏ i : Fin j, (t + quadraticCoordinate (B i))) /
              (∏ i : Fin (j + 1), (t + quadraticCoordinate (A i))) := by sorry
