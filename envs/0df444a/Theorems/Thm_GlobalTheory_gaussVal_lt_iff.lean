-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_lt_iff
-- name    : GlobalTheory.gaussVal_lt_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:37.164098+00:00
-- url     : https://prove2.me/theorems/f2c2c152-4f2f-4725-ac30-735dbeb9266f
-- title:
--   Global Theory: gauss Val lt iff
-- statement:
--   The Global Theory construction uses the gauss Val lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L191-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L191-L192

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
open MvPolynomial
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

theorem GlobalTheory.gaussVal_lt_iff {f : MvPolynomial σ R} {γ : Γ₀} (hγ : γ ≠ 0) :
    gaussVal v f < γ ↔ ∀ m, v (coeff m f) < γ := by sorry
