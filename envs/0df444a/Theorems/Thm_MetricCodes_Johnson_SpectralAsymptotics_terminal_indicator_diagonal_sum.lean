-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminal_indicator_diagonal_sum
-- name    : MetricCodes.Johnson.SpectralAsymptotics.terminal_indicator_diagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/d06c0813-ac7a-4b92-9d29-b00ee3eb7eba
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.terminal_indicator_diagonal_sum
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

theorem MetricCodes.Johnson.SpectralAsymptotics.terminal_indicator_diagonal_sum
    (d m : ℕ) (hm : m ≤ d) (b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) =
      ∑ r ∈ Finset.range (m + 1), b (d - m + r) := by sorry
