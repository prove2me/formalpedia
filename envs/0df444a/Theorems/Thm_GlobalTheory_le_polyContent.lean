-- Prove2me | Theorems.Thm_GlobalTheory_le_polyContent
-- name    : GlobalTheory.le_polyContent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:32.866186+00:00
-- url     : https://prove2.me/theorems/f265d2fd-7b35-4dee-8080-d385c5bf620b
-- title:
--   Global Theory: le poly Content
-- statement:
--   The Global Theory construction uses the le poly Content property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L750-L751
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L750-L751

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

theorem GlobalTheory.le_polyContent (c : (σ →₀ ℕ) →₀ M) (m : σ →₀ ℕ) :
    basisVal v b (c m) ≤ polyContent v b c := by sorry
