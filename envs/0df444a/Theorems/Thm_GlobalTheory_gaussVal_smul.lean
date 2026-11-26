-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_smul
-- name    : GlobalTheory.gaussVal_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:15.427065+00:00
-- url     : https://prove2.me/theorems/4ac6a379-a5d0-4da8-a8ab-c44d0265142f
-- title:
--   Global Theory: gauss Val smul
-- statement:
--   The Global Theory construction uses the gauss Val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L216-L218

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

theorem GlobalTheory.gaussVal_smul (a : R) (f : MvPolynomial σ R) :
    gaussVal v (a • f) = v a * gaussVal v f := by sorry
