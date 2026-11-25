-- Prove2me | Theorems.Thm_GlobalTheory_polyContent_eq_zero_iff
-- name    : GlobalTheory.polyContent_eq_zero_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:49:31.819919+00:00
-- url     : https://prove2.me/theorems/0fff1a9f-f057-47c0-8f34-c48f9d3cf309
-- title:
--   Global Theory: poly Content eq zero iff
-- statement:
--   The Global Theory construction uses the poly Content eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L761-L764
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L761-L764

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

theorem GlobalTheory.polyContent_eq_zero_iff (hv : v.supp = ⊥) {c : (σ →₀ ℕ) →₀ M} :
    polyContent v b c = 0 ↔ c = 0 := by sorry
