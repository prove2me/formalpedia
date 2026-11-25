-- Prove2me | Theorems.Thm_GlobalTheory_gaussAbs_eq_gaussNorm
-- name    : GlobalTheory.gaussAbs_eq_gaussNorm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:20.028709+00:00
-- url     : https://prove2.me/theorems/bb0885ec-538d-46ca-b217-1459080d0062
-- title:
--   Global Theory: gauss Abs eq gauss Norm
-- statement:
--   The Global Theory construction uses the gauss Abs eq gauss Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L618-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L618-L629

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

theorem GlobalTheory.gaussAbs_eq_gaussNorm (f : MvPolynomial σ R) :
    gaussAbs a ha f = MvPowerSeries.gaussNorm a (fun _ => 1) (f : MvPowerSeries σ R) := by sorry
