-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_gtChannelCharacteristic_derivative_eval_pos
-- name    : MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.gtChannelCharacteristic_derivative_eval_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/7fecc177-95bf-469b-8fba-ef752e0e21b1
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.gtChannelCharacteristic_derivative_eval_pos
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

theorem MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.gtChannelCharacteristic_derivative_eval_pos {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
        (ambientShift n lam row) =
      activeDenominator (ambientShift n lam) row := by sorry
