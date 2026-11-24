-- Prove2me | Theorems.Thm_GlobalTheory_Chow_mem_elimIdeal_iff_forall
-- name    : GlobalTheory.Chow.mem_elimIdeal_iff_forall
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:10:14.683348+00:00
-- url     : https://prove2.me/theorems/c8e16442-fabe-46b1-9121-0a62836acefb
-- title:
--   Chow: mem elim Ideal iff forall
-- statement:
--   The Chow construction uses the mem elim Ideal iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L61-L69

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

theorem GlobalTheory.Chow.mem_elimIdeal_iff_forall {p : Ideal (MvPolynomial σ K)} {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔ ∀ j, ∃ m : ℕ, map C f * C (X j ^ m) ∈ incidenceIdeal β p := by sorry
