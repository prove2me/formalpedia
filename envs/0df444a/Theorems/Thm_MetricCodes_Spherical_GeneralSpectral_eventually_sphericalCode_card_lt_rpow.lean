-- Prove2me | Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_sphericalCode_card_lt_rpow
-- name    : MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:37.266213+00:00
-- url     : https://prove2.me/theorems/cd01f9f9-c70e-4596-911b-f672525d210c
-- title:
--   MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral

theorem MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
    {s a b r : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b)
    (hr : MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b < r) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (r * (n : ℝ)) := by sorry
