-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Rate_binaryRate_le_shellRate_of_projectionGrams
-- name    : MetricCodes.Johnson.Rate.binaryRate_le_shellRate_of_projectionGrams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/ffcbf594-6c92-4da9-b6bb-5e1ea1300de9
-- title:
--   MetricCodes.Johnson.Rate.binaryRate_le_shellRate_of_projectionGrams
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Rate
open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics

theorem MetricCodes.Johnson.Rate.binaryRate_le_shellRate_of_projectionGrams
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u)
    (hdata : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.shellRate a b g u := by sorry
