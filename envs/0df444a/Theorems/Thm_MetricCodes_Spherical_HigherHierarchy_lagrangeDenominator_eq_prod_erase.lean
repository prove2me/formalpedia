-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeDenominator_eq_prod_erase
-- name    : MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_eq_prod_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:30.752311+00:00
-- url     : https://prove2.me/theorems/2b757c8a-45f8-447d-a664-97069c61767a
-- title:
--   MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_eq_prod_erase
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy

theorem MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_eq_prod_erase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ =
      ∏ j ∈ Finset.univ.erase ℓ,
        (quadraticCoordinate (a ℓ) - quadraticCoordinate (a j)) := by sorry
