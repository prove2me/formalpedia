-- Prove2me | Theorems.Thm_GlobalTheory_Chow_mem_elimIdeal_iff_of_generic
-- name    : GlobalTheory.Chow.mem_elimIdeal_iff_of_generic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:50.534926+00:00
-- url     : https://prove2.me/theorems/fee0921d-f17c-4e12-9d08-61d820d81176
-- title:
--   Chow: mem elim Ideal iff of generic
-- statement:
--   The Chow construction uses the mem elim Ideal iff of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L177-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L177-L220

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

theorem GlobalTheory.Chow.mem_elimIdeal_iff_of_generic {F : Type*} [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p) (hne : ξ ≠ 0)
    {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔
      map (algebraMap K F) f ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by sorry
