-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_localized_minimizer_of_lsc_and_smallEntropy
-- name    : MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_minimizer_of_lsc_and_smallEntropy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:40.58935+00:00
-- url     : https://prove2.me/theorems/eb6a0230-c1d4-45ff-a7d0-08454e01cc64
-- title:
--   MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_minimizer_of_lsc_and_smallEntropy
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
open Set Filter Topology

theorem MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hzero : κ 0 = 0)
    (hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      κ t ≤ MetricCodes.sphericalEntropy (t ^ 2))
    (hlsc : LowerSemicontinuousOn κ (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by sorry
