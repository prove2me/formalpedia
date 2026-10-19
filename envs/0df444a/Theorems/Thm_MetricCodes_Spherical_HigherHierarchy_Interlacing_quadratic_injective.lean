-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_injective
-- name    : MetricCodes.Spherical.HigherHierarchy.Interlacing.quadratic_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:30.752311+00:00
-- url     : https://prove2.me/theorems/a9e482ea-77e7-4116-b548-0ecf4d16f29e
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Interlacing.quadratic_injective
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

theorem MetricCodes.Spherical.HigherHierarchy.Interlacing.quadratic_injective {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    Function.Injective (fun i => quadraticCoordinate (a i)) := by sorry
