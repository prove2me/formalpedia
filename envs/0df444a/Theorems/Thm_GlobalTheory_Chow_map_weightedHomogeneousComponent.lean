-- Prove2me | Theorems.Thm_GlobalTheory_Chow_map_weightedHomogeneousComponent
-- name    : GlobalTheory.Chow.map_weightedHomogeneousComponent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:59.253529+00:00
-- url     : https://prove2.me/theorems/4fc66281-0535-4703-ad64-406302c91f94
-- title:
--   Chow: map weighted Homogeneous Component
-- statement:
--   The Chow construction uses the map weighted Homogeneous Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L335-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L335-L341

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

theorem GlobalTheory.Chow.map_weightedHomogeneousComponent {S τ M : Type*} [CommRing S] [AddCommMonoid M]
    (φ : K →+* S) (w : τ → M) (a : M) (f : MvPolynomial τ K) :
    map φ (weightedHomogeneousComponent w a f) = weightedHomogeneousComponent w a (map φ f) := by sorry
