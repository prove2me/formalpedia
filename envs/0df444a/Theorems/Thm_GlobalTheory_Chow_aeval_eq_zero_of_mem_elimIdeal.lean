-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_mem_elimIdeal
-- name    : GlobalTheory.Chow.aeval_eq_zero_of_mem_elimIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:27.309795+00:00
-- url     : https://prove2.me/theorems/4c315de3-975a-460b-84e8-b94532606649
-- title:
--   Chow: aeval eq zero of mem elim Ideal
-- statement:
--   The Chow construction uses the aeval eq zero of mem elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L71-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L71-L91

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

theorem GlobalTheory.Chow.aeval_eq_zero_of_mem_elimIdeal {G : Type*} [CommRing G] [IsDomain G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (hne : ξ ≠ 0)
    {t : β × σ → G} (ht : ∀ i, ∑ j, t (i, j) * ξ j = 0)
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) : aeval t f = 0 := by sorry
