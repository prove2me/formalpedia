-- Prove2me | Theorems.Thm_GlobalTheory_Chow_incidenceIdeal_le
-- name    : GlobalTheory.Chow.incidenceIdeal_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:11.858596+00:00
-- url     : https://prove2.me/theorems/216e2b11-7210-476b-af5a-7cc7085ef798
-- title:
--   Chow: incidence Ideal le
-- statement:
--   The Chow construction uses the incidence Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L36-L40

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

theorem GlobalTheory.Chow.incidenceIdeal_le {p : Ideal (MvPolynomial σ K)}
    {J : Ideal (MvPolynomial (β × σ) (MvPolynomial σ K))} :
    incidenceIdeal β p ≤ J ↔ (∀ g ∈ p, C g ∈ J) ∧ ∀ i, genericForm K σ i ∈ J := by sorry
