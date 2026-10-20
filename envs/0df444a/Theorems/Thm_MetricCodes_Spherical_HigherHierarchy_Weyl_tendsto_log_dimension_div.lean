-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_dimension_div
-- name    : MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_dimension_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/a0a35b56-1266-4aee-98ea-b5d7c518a510
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_dimension_div
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
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl

theorem MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_dimension_div
    {r : ℕ} (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i)
    (hanti : StrictAnti a)
    (hdominant : ∀ n, Antitone (lam n))
    (hTop : ∀ i, Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlim : ∀ i,
      Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
        atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ => Real.log (dimension n (lam n)) / (n : ℝ))
      atTop
      (𝓝 (∑ i : Fin (r + 1),
        ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i)))) := by sorry
