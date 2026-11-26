-- Prove2me | Theorems.Thm_GlobalTheory_gaussAbs_rename
-- name    : GlobalTheory.gaussAbs_rename
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:09.547466+00:00
-- url     : https://prove2.me/theorems/8b6e8e10-57a4-49dd-843e-30e5207c43a7
-- title:
--   Global Theory: gauss Abs rename
-- statement:
--   The Global Theory construction uses the gauss Abs rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L609-L611
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L609-L611

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

theorem GlobalTheory.gaussAbs_rename {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAbs a ha (rename e f) = gaussAbs a ha f := by sorry
