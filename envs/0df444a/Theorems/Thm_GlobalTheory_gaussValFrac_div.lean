-- Prove2me | Theorems.Thm_GlobalTheory_gaussValFrac_div
-- name    : GlobalTheory.gaussValFrac_div
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:09.252111+00:00
-- url     : https://prove2.me/theorems/7e2b684f-4505-4c64-aa8d-684a5ea7b937
-- title:
--   Global Theory: gauss Val Frac div
-- statement:
--   The Global Theory construction uses the gauss Val Frac div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L435-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L435-L437

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

theorem GlobalTheory.gaussValFrac_div (f g : MvPolynomial σ K) :
    gaussValFrac v σ F (algebraMap _ F f / algebraMap _ F g) = gaussVal v f / gaussVal v g := by sorry
