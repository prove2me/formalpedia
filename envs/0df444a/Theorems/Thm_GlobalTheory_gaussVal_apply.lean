-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_apply
-- name    : GlobalTheory.gaussVal_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:32.297192+00:00
-- url     : https://prove2.me/theorems/318e122b-4b81-4c8d-b45b-d0070ac2a5df
-- title:
--   Global Theory: gauss Val apply
-- statement:
--   The Global Theory construction uses the gauss Val apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L182-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L182-L183

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

theorem GlobalTheory.gaussVal_apply (f : MvPolynomial σ R) :
    gaussVal v f = f.support.sup fun m => v (coeff m f) := by sorry
