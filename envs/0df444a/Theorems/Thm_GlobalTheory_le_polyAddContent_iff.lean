-- Prove2me | Theorems.Thm_GlobalTheory_le_polyAddContent_iff
-- name    : GlobalTheory.le_polyAddContent_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:24.569661+00:00
-- url     : https://prove2.me/theorems/f5c87c4a-75cc-44ac-ba28-6f867cb4ad08
-- title:
--   Global Theory: le poly Add Content iff
-- statement:
--   The Global Theory construction uses the le poly Add Content iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L947-L950
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L947-L950

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
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)

theorem GlobalTheory.le_polyAddContent_iff {c : (σ →₀ ℕ) →₀ M} {γ : Γ} :
    γ ≤ polyAddContent v b c ↔ ∀ m, γ ≤ basisAddVal v b (c m) := by sorry
