-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_channelFactor_of_ratios
-- name    : MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_channelFactor_of_ratios
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/c1d42377-cd0d-42d5-80f7-c55a4c3c547c
-- title:
--   MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_channelFactor_of_ratios
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_channelFactor_of_ratios {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) (j : Fin r) (c d : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((ambientShift n (lam n) i + c) ^ 2 -
          stabilizerShift n (mu n) j ^ 2) /
          ((ambientShift n (lam n) i + d) ^ 2 -
            ambientShift n (lam n) (i.succAbove j) ^ 2)))
      atTop
      (𝓝 ((quadraticCoordinate (a i) - quadraticCoordinate (b j)) /
        (quadraticCoordinate (a i) -
          quadraticCoordinate (a (i.succAbove j))))) := by sorry
