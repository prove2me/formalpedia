-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalRayleigh_le_top
-- name    : MetricCodes.Johnson.SpectralAsymptotics.terminalRayleigh_le_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/3eb5d722-8fe8-4d7d-acae-0336b3184fba
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.terminalRayleigh_le_top
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

theorem MetricCodes.Johnson.SpectralAsymptotics.terminalRayleigh_le_top
    (a b g u : ℝ) (m n : ℕ)
    (hfit : supportDegree b n + complementDegree g n + m ≤
      terminalDegree u n) :
    terminalRayleigh a b g u m n ≤
      MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by sorry
