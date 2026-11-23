-- Prove2me | Theorems.Thm_GlobalTheory_Chow_genericPoint_ne_zero
-- name    : GlobalTheory.Chow.genericPoint_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:41.8284+00:00
-- url     : https://prove2.me/theorems/c2c81880-aee0-4e06-a144-abe3945191ee
-- title:
--   Chow: generic Point ne zero
-- statement:
--   The Chow construction uses the generic Point ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L239-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L239-L243

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
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
omit [Fintype σ]

theorem GlobalTheory.Chow.genericPoint_ne_zero {p : Ideal (MvPolynomial σ K)} (hp : ∃ j, X j ∉ p) :
    genericPoint p ≠ 0 := by sorry
