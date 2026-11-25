-- Prove2me | Theorems.Thm_GlobalTheory_gaussValAlg_apply
-- name    : GlobalTheory.gaussValAlg_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:37.636103+00:00
-- url     : https://prove2.me/theorems/d32b5ffb-eb28-4882-8924-38c31d9d9d5c
-- title:
--   Global Theory: gauss Val Alg apply
-- statement:
--   The Global Theory construction uses the gauss Val Alg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L153-L154

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
variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [AddMonoid G] [UniqueSums G]

theorem GlobalTheory.gaussValAlg_apply (f : AddMonoidAlgebra R G) :
    gaussValAlg v f = f.coeff.support.sup fun m => v (f.coeff m) := by sorry
