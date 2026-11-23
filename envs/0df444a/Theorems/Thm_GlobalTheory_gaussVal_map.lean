-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_map
-- name    : GlobalTheory.gaussVal_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:24.937104+00:00
-- url     : https://prove2.me/theorems/311c6a49-c47c-4c51-84ac-c46f8445b086
-- title:
--   Global Theory: gauss Val map
-- statement:
--   The Global Theory construction uses the gauss Val map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L248-L250

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

theorem GlobalTheory.gaussVal_map (w : Valuation S Γ₀) (φ : R →+* S) (f : MvPolynomial σ R) :
    gaussVal w (map φ f) = gaussVal (w.comap φ) f := by sorry
