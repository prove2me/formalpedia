-- Prove2me | Theorems.Thm_GlobalTheory_polyContent_le_iff_coord
-- name    : GlobalTheory.polyContent_le_iff_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:36.359783+00:00
-- url     : https://prove2.me/theorems/bc1400dc-0b3f-4b46-bdb8-82fa726841a4
-- title:
--   Global Theory: poly Content le iff coord
-- statement:
--   The Global Theory construction uses the poly Content le iff coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L746-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L746-L748

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

theorem GlobalTheory.polyContent_le_iff_coord {c : (σ →₀ ℕ) →₀ M} {γ : Γ₀} :
    polyContent v b c ≤ γ ↔ ∀ m i, v (b.repr (c m) i) ≤ γ := by sorry
