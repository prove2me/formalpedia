-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_map_of_eq
-- name    : GlobalTheory.gaussVal_map_of_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:54.771537+00:00
-- url     : https://prove2.me/theorems/bab05017-b98a-4de5-90ac-dc60e39eeedd
-- title:
--   Global Theory: gauss Val map of eq
-- statement:
--   The Global Theory construction uses the gauss Val map of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L252-L254

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

theorem GlobalTheory.gaussVal_map_of_eq (w : Valuation S Γ₀) (φ : R →+* S) (h : ∀ a, w (φ a) = v a)
    (f : MvPolynomial σ R) : gaussVal w (map φ f) = gaussVal v f := by sorry
