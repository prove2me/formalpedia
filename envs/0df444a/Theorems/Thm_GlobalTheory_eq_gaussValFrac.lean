-- Prove2me | Theorems.Thm_GlobalTheory_eq_gaussValFrac
-- name    : GlobalTheory.eq_gaussValFrac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:39.741811+00:00
-- url     : https://prove2.me/theorems/cc7cc4d2-0ef2-46d8-83ff-2100b0dc785d
-- title:
--   Global Theory: eq gauss Val Frac
-- statement:
--   The Global Theory construction uses the eq gauss Val Frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L449-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L449-L454

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
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

theorem GlobalTheory.eq_gaussValFrac {w : Valuation F Γ₀}
    (h : ∀ f : MvPolynomial σ K, w (algebraMap _ F f) = gaussVal v f) :
    w = gaussValFrac v σ F := by sorry
