-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_rayleigh
-- name    : MetricCodes.Johnson.SpectralAsymptotics.terminalVector_rayleigh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/4442a407-e45f-4f59-8659-f7ad61c0c464
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.terminalVector_rayleigh
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

theorem MetricCodes.Johnson.SpectralAsymptotics.terminalVector_rayleigh
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    MetricCodes.Johnson.rayleigh n w p q L (terminalVector p q L m) =
      ((∑ r ∈ Finset.range (m + 1),
          MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
        2 * ∑ r ∈ Finset.range m,
          MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
        ((m : ℝ) + 1) := by sorry
