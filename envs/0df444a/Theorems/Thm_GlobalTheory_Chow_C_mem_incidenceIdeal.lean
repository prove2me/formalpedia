-- Prove2me | Theorems.Thm_GlobalTheory_Chow_C_mem_incidenceIdeal
-- name    : GlobalTheory.Chow.C_mem_incidenceIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:59.130894+00:00
-- url     : https://prove2.me/theorems/4f40b53e-9ea6-4cf6-bf8f-e135133a045c
-- title:
--   Chow: C mem incidence Ideal
-- statement:
--   The Chow construction uses the C mem incidence Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L28-L30

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
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]

theorem GlobalTheory.Chow.C_mem_incidenceIdeal {p : Ideal (MvPolynomial σ K)} {g : MvPolynomial σ K} (hg : g ∈ p) :
    C g ∈ incidenceIdeal β p := by sorry
