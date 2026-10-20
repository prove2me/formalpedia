-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowFirstAxisIntertwining_sum_powerset_erase_insert
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining.sum_powerset_erase_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/f6fccd11-3013-4878-9fda-b088d6cdad03
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining.sum_powerset_erase_insert
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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining.sum_powerset_erase_insert
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (a : α) (ha : a ∈ P) (f : Finset α → M) :
    (∑ S ∈ P.powerset, f S) =
      ∑ S ∈ (P.erase a).powerset, (f S + f (insert a S)) := by sorry
