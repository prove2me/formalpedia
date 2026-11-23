-- Prove2me | Theorems.Thm_GlobalTheory_Chow_map_mem_span_linForm
-- name    : GlobalTheory.Chow.map_mem_span_linForm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:37.505365+00:00
-- url     : https://prove2.me/theorems/a6bda00e-f989-4635-9b8f-3d9a5889c7e9
-- title:
--   Chow: map mem span lin Form
-- statement:
--   The Chow construction uses the map mem span lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L165-L173

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

theorem GlobalTheory.Chow.map_mem_span_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u : σ → R}
    {h : MvPolynomial (β × σ) R} (hh : h ∈ Ideal.span (Set.range (linForm u : β → _))) :
    map φ h ∈ Ideal.span (Set.range (linForm (fun j => φ (u j)) : β → _)) := by sorry
