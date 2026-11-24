-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_sum_le
-- name    : GlobalTheory.basisVal_sum_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:04.727553+00:00
-- url     : https://prove2.me/theorems/e0074c3c-f8ff-4dbf-9c28-c1dcbbba2125
-- title:
--   Global Theory: basis Val sum le
-- statement:
--   The Global Theory construction uses the basis Val sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L691-L695
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L691-L695

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

theorem GlobalTheory.basisVal_sum_le {α : Type*} {s : Finset α} {x : α → M} {γ : Γ₀}
    (h : ∀ a ∈ s, basisVal v b (x a) ≤ γ) : basisVal v b (∑ a ∈ s, x a) ≤ γ := by sorry
