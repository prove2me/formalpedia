-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_gaussValFrac_sumAlgEquiv
-- name    : GlobalTheory.gaussVal_gaussValFrac_sumAlgEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:57.62111+00:00
-- url     : https://prove2.me/theorems/0e7f3c06-66b6-430d-a2ec-6b29850c6dec
-- title:
--   Global Theory: gauss Val gauss Val Frac sum Alg Equiv
-- statement:
--   The Global Theory construction uses the gauss Val gauss Val Frac sum Alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L480-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L480-L483

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

theorem GlobalTheory.gaussVal_gaussValFrac_sumAlgEquiv (f : MvPolynomial (τ ⊕ σ) K) :
    gaussVal (gaussValFrac v σ F) (map (algebraMap _ F) (sumAlgEquiv K τ σ f)) =
      gaussVal v f := by sorry
