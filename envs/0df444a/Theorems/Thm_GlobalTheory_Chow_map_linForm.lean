-- Prove2me | Theorems.Thm_GlobalTheory_Chow_map_linForm
-- name    : GlobalTheory.Chow.map_linForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:52.638836+00:00
-- url     : https://prove2.me/theorems/01bb76da-a855-48b8-a268-172b1ee1080b
-- title:
--   Chow: map lin Form
-- statement:
--   The Chow construction uses the map lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L161-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L161-L163

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

theorem GlobalTheory.Chow.map_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : σ → R) (i : β) :
    map φ (linForm u i) = linForm (fun j => φ (u j)) i := by sorry
