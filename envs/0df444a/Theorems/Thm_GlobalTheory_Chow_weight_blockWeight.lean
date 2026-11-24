-- Prove2me | Theorems.Thm_GlobalTheory_Chow_weight_blockWeight
-- name    : GlobalTheory.Chow.weight_blockWeight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:43.352486+00:00
-- url     : https://prove2.me/theorems/35a3558f-9932-4de8-b88c-664c02dd2667
-- title:
--   Chow: weight block Weight
-- statement:
--   The Chow construction uses the weight block Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L270-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L270-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']

theorem GlobalTheory.Chow.weight_blockWeight [Fintype σ] (d : β × σ →₀ ℕ) (i : β) :
    Finsupp.weight blockWeight d i = ∑ j, d (i, j) := by sorry
