-- Prove2me | Theorems.Thm_GlobalTheory_gaussValFrac_le_one_iff
-- name    : GlobalTheory.gaussValFrac_le_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:56.516676+00:00
-- url     : https://prove2.me/theorems/13cd7c60-ea98-497b-8242-c587c69265d2
-- title:
--   Global Theory: gauss Val Frac le one iff
-- statement:
--   The Global Theory construction uses the gauss Val Frac le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L462-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L462-L478

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

theorem GlobalTheory.gaussValFrac_le_one_iff {x : F} :
    gaussValFrac v σ F x ≤ 1 ↔ ∃ f g : MvPolynomial σ K, gaussVal v f ≤ 1 ∧ gaussVal v g = 1 ∧
      x = algebraMap _ F f / algebraMap _ F g := by sorry
