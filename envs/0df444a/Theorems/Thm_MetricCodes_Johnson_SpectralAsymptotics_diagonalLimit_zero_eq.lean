-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_diagonalLimit_zero_eq
-- name    : MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_zero_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/3cb1f64a-d38c-418d-a26c-9e5530634b57
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_zero_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics

theorem MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_zero_eq
    {d a b g u : ℝ}
    (_h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a 0 0 u =
      MetricCodes.Johnson.centeredWeight a ^ 2 *
        (1 - MetricCodes.Johnson.centeredDegree u ^ 2) /
        (MetricCodes.Johnson.centeredDegree u ^ 2 *
          (1 - MetricCodes.Johnson.centeredWeight a ^ 2)) := by sorry
