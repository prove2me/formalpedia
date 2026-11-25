-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_eq_sup_univ
-- name    : GlobalTheory.basisVal_eq_sup_univ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:30.249594+00:00
-- url     : https://prove2.me/theorems/bf0be660-7dea-4997-bf5c-ecadc6722f85
-- title:
--   Global Theory: basis Val eq sup univ
-- statement:
--   The Global Theory construction uses the basis Val eq sup univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L666-L668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L666-L668

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

theorem GlobalTheory.basisVal_eq_sup_univ [Fintype ι] (x : M) :
    basisVal v b x = Finset.univ.sup fun i => v (b.repr x i) := by sorry
