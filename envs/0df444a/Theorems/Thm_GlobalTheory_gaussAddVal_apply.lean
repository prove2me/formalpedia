-- Prove2me | Theorems.Thm_GlobalTheory_gaussAddVal_apply
-- name    : GlobalTheory.gaussAddVal_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:11.583566+00:00
-- url     : https://prove2.me/theorems/3423258f-d73a-46a6-a0ff-4e600b34fc02
-- title:
--   Global Theory: gauss Add Val apply
-- statement:
--   The Global Theory construction uses the gauss Add Val apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L501-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L501-L508

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

theorem GlobalTheory.gaussAddVal_apply (f : MvPolynomial σ R) :
    gaussAddVal v f = f.support.inf fun m => v (coeff m f) := by sorry
