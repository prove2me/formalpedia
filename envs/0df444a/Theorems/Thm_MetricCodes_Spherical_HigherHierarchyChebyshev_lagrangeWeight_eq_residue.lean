-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_lagrangeWeight_eq_residue
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.lagrangeWeight_eq_residue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/bbdd9f0c-070f-460c-a076-300848bae234
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.lagrangeWeight_eq_residue
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.lagrangeWeight_eq_residue {R : ℝ} (hR : 0 < R)
    (r : ℕ) (ℓ : Fin (r + 1)) :
    MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
      (ambient R r) (stabilizer R r) ℓ = residue (r + 1) := by sorry
