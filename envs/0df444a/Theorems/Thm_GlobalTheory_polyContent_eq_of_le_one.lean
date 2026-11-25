-- Prove2me | Theorems.Thm_GlobalTheory_polyContent_eq_of_le_one
-- name    : GlobalTheory.polyContent_eq_of_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:34.828559+00:00
-- url     : https://prove2.me/theorems/ecb23aa2-b41f-5a5c-b5ff-e4635054e094
-- title:
--   Global Theory: poly Content eq of le one
-- statement:
--   The Global Theory construction uses the poly Content eq of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L766-L769
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L766-L769

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

theorem GlobalTheory.polyContent_eq_of_le_one (b' : Basis κ R M) (h : ∀ i, basisVal v b' (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (b' j) ≤ 1) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b c = polyContent v b' c := by sorry
