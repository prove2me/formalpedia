-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_shiftedRowGap_raiseWeight_of_ne
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift.shiftedRowGap_raiseWeight_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/a6a33684-2512-4557-bb8e-ead9daa24c7f
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift.shiftedRowGap_raiseWeight_of_ne
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift.shiftedRowGap_raiseWeight_of_ne
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (target preceding raised : Fin (r + 1))
    (htarget : target ≠ raised) (hpreceding : preceding ≠ raised) :
    shiftedRowGap (raiseWeight lam raised) target preceding =
      shiftedRowGap lam target preceding := by sorry
