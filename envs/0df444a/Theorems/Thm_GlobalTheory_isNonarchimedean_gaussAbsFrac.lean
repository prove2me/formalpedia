-- Prove2me | Theorems.Thm_GlobalTheory_isNonarchimedean_gaussAbsFrac
-- name    : GlobalTheory.isNonarchimedean_gaussAbsFrac
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:36.394447+00:00
-- url     : https://prove2.me/theorems/df780f9b-e9d6-4299-a981-bdb006a8ac67
-- title:
--   Global Theory: is Nonarchimedean gauss Abs Frac
-- statement:
--   The Global Theory construction uses the is Nonarchimedean gauss Abs Frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L644-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L644-L645

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
variable {K : Type*} [Field K] (a : AbsoluteValue K ℝ) (ha : IsNonarchimedean a)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

theorem GlobalTheory.isNonarchimedean_gaussAbsFrac : IsNonarchimedean (gaussAbsFrac a ha σ F) := by sorry
