-- Prove2me | Theorems.Thm_MetricCodes_Hamming_spectralMarginPolynomial_continuous
-- name    : MetricCodes.Hamming.spectralMarginPolynomial_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:21.918845+00:00
-- url     : https://prove2.me/theorems/709a3920-66ce-4b5d-9fcc-26b5d2097ac1
-- title:
--   MetricCodes.Hamming.spectralMarginPolynomial_continuous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming

theorem MetricCodes.Hamming.spectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (spectralMarginPolynomial a c) := by sorry
