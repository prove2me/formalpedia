-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_eq_of_forall_le_one
-- name    : GlobalTheory.basisVal_eq_of_forall_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:16.07682+00:00
-- url     : https://prove2.me/theorems/0afd8972-6b4b-434b-8ab4-1b50d0595aa6
-- title:
--   Global Theory: basis Val eq of forall le one
-- statement:
--   The Global Theory construction uses the basis Val eq of forall le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L732-L735
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L732-L735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (b : Basis ι R M)

theorem GlobalTheory.basisVal_eq_of_forall_le_one (hv : ∀ a, v a ≤ 1) (c : Basis κ R M) (x : M) :
    basisVal v b x = basisVal v c x := by sorry
