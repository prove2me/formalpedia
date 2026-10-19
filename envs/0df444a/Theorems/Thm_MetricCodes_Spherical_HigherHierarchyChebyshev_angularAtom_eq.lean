-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAtom_eq
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/38d787d9-0dee-4c86-81d6-20ffcd03d903
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_eq {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    angularAtom R t =
      Real.sqrt R * Real.cos (Real.pi * t / 2) /
        Real.sqrt (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) := by sorry
