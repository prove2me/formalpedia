-- Prove2me | Theorems.Thm_GlobalTheory_isGreatest_basisVal
-- name    : GlobalTheory.isGreatest_basisVal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:08.392175+00:00
-- url     : https://prove2.me/theorems/c5c71357-8581-53d1-a15a-fea7291f3c01
-- title:
--   Global Theory: is Greatest basis Val
-- statement:
--   The Global Theory construction uses the is Greatest basis Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L717-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L717-L726

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

theorem GlobalTheory.isGreatest_basisVal (x : M) :
    IsGreatest {γ | ∃ φ : M →ₗ[R] R, (∀ y, basisVal v b y ≤ 1 → v (φ y) ≤ 1) ∧ v (φ x) = γ}
      (basisVal v b x) := by sorry
