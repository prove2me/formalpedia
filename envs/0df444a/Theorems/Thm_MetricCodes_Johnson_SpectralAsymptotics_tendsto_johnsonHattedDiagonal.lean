-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonHattedDiagonal
-- name    : MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonHattedDiagonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/1d7506e3-e78e-4175-b3f2-e70415eb1606
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonHattedDiagonal
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

theorem MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonHattedDiagonal
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedDiagonalLimit a b g u)) := by sorry
