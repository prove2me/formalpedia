-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_characteristicResidue_scaled_unique_of_resolvent
-- name    : MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.characteristicResidue_scaled_unique_of_resolvent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/54a0385b-afea-4d1c-8891-f84c23d9dc88
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.characteristicResidue_scaled_unique_of_resolvent
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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.characteristicResidue_scaled_unique_of_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (hinjective : Function.Injective nodes)
    (numerator : Polynomial ℝ) (weight : ι → ℝ) (scale : ℝ)
    (hresolvent : ∀ z : ℝ, (∀ i : ι, z ≠ nodes i) →
      scale * numerator.eval z /
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).eval z =
        ∑ i : ι, weight i / (z - nodes i))
    (i : ι) :
    weight i = scale * numerator.eval (nodes i) /
      (Lagrange.nodal (Finset.univ : Finset ι) nodes).derivative.eval
        (nodes i) := by sorry
