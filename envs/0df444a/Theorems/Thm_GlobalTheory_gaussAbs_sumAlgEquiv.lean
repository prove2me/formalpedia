-- Prove2me | Theorems.Thm_GlobalTheory_gaussAbs_sumAlgEquiv
-- name    : GlobalTheory.gaussAbs_sumAlgEquiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:19.943994+00:00
-- url     : https://prove2.me/theorems/dcebf638-8860-49b3-9c8b-a2c7731c13ad
-- title:
--   Global Theory: gauss Abs sum Alg Equiv
-- statement:
--   The Global Theory construction uses the gauss Abs sum Alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L613-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L613-L616

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

theorem GlobalTheory.gaussAbs_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAbs (gaussAbs a ha) (isNonarchimedean_gaussAbs a ha) (sumAlgEquiv R σ τ f) =
      gaussAbs a ha f := by sorry
