-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tridiagonal_quadratic_sum
-- name    : MetricCodes.Johnson.SpectralAsymptotics.tridiagonal_quadratic_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/a318e31a-88a5-4888-816f-bfb744ba4b41
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.tridiagonal_quadratic_sum
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

theorem MetricCodes.Johnson.SpectralAsymptotics.tridiagonal_quadratic_sum
    (d : ℕ) (b c v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      (∑ i ∈ Finset.range (d + 1), b i * v i ^ 2) +
        2 * ∑ i ∈ Finset.range d, c i * v i * v (i + 1) := by sorry
