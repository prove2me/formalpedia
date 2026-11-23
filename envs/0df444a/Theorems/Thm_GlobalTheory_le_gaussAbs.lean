-- Prove2me | Theorems.Thm_GlobalTheory_le_gaussAbs
-- name    : GlobalTheory.le_gaussAbs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:50.539252+00:00
-- url     : https://prove2.me/theorems/7a97bd46-0de4-4f15-8892-9ae832973b0c
-- title:
--   Global Theory: le gauss Abs
-- statement:
--   The Global Theory construction uses the le gauss Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L590-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L590-L591

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
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)

theorem GlobalTheory.le_gaussAbs (f : MvPolynomial σ R) (m : σ →₀ ℕ) : a (coeff m f) ≤ gaussAbs a ha f := by sorry
