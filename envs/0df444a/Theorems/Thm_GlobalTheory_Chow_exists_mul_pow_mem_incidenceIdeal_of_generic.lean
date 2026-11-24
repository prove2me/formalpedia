-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_mul_pow_mem_incidenceIdeal_of_generic
-- name    : GlobalTheory.Chow.exists_mul_pow_mem_incidenceIdeal_of_generic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:10:08.183233+00:00
-- url     : https://prove2.me/theorems/6d908ede-37e1-4906-aa0b-7bda799c8a65
-- title:
--   Chow: exists mul pow mem incidence Ideal of generic
-- statement:
--   The Chow construction uses the exists mul pow mem incidence Ideal of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L10-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeSaturationGenericHyperplaneSection
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

theorem GlobalTheory.Chow.exists_mul_pow_mem_incidenceIdeal_of_generic {σ β K F : Type*} [Fintype σ] [CommRing K]
    [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p)
    {h : MvPolynomial (β × σ) (MvPolynomial σ K)}
    (hf : map (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom h ∈
      Ideal.span (Set.range (linForm ξ : β → _))) (j : σ) :
    ∃ m : ℕ, h * C (X j ^ m) ∈ incidenceIdeal β p := by sorry
