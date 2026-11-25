-- Prove2me | Theorems.Thm_GlobalTheory_gaussAbs_le_iff
-- name    : GlobalTheory.gaussAbs_le_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:01.169582+00:00
-- url     : https://prove2.me/theorems/f0b4a2c8-73f9-47f0-82aa-bb636b96620a
-- title:
--   Global Theory: gauss Abs le iff
-- statement:
--   The Global Theory construction uses the gauss Abs le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L597-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L597-L601

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

theorem GlobalTheory.gaussAbs_le_iff {f : MvPolynomial σ R} {r : ℝ} :
    gaussAbs a ha f ≤ r ↔ ∀ m, a (coeff m f) ≤ r := by sorry
