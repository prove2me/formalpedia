-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/a8041806-3f3a-4837-b55e-4b48644b30dd
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
    {r j : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A B) (c : ℝ)
    (hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c * stieltjesPhaseProduct A B t))) :
    Tendsto (fun n => 1 - 2 * Gamma (a n) (b n))
      atTop (𝓝 (c * (1 - 2 * Gamma A B))) := by sorry
