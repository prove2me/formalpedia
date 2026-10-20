-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_arcsine_normalizer
-- name    : MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_arcsine_normalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:35.827193+00:00
-- url     : https://prove2.me/theorems/c8f11e2d-5fba-40c9-a71c-b7ae064c2976
-- title:
--   MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_arcsine_normalizer
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_arcsine_normalizer {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4))) :
    Entropy.phaseNormalizer (stieltjesPhase a b) =
      1 - 2 * Gamma a b := by sorry
