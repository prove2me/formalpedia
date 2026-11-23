-- Prove2me | Theorems.Thm_GlobalTheory_polyContent_le_iff
-- name    : GlobalTheory.polyContent_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:45.435214+00:00
-- url     : https://prove2.me/theorems/20372f73-e560-4762-8147-759e9f5cb875
-- title:
--   Global Theory: poly Content le iff
-- statement:
--   The Global Theory construction uses the poly Content le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L742-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L742-L744

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

theorem GlobalTheory.polyContent_le_iff {c : (σ →₀ ℕ) →₀ M} {γ : Γ₀} :
    polyContent v b c ≤ γ ↔ ∀ m, basisVal v b (c m) ≤ γ := by sorry
