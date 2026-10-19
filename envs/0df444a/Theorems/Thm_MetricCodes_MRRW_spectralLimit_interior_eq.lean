-- Prove2me | Theorems.Thm_MetricCodes_MRRW_spectralLimit_interior_eq
-- name    : MetricCodes.MRRW.spectralLimit_interior_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/a8448bca-6549-43df-846c-385257474ae9
-- title:
--   MetricCodes.MRRW.spectralLimit_interior_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology

theorem MetricCodes.MRRW.spectralLimit_interior_eq (a u e : ℝ) :
    MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u =
      let z := MetricCodes.Johnson.centeredDegree u
      let m := MetricCodes.Johnson.centeredWeight (interiorWeight a u e)
      let t := 1 - 2 * e
      (m * (t ^ 2 - z ^ 2)) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - (m * t) ^ 2) * (t ^ 2 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) := by sorry
