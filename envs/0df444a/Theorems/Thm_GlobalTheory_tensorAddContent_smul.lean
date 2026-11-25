-- Prove2me | Theorems.Thm_GlobalTheory_tensorAddContent_smul
-- name    : GlobalTheory.tensorAddContent_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:30.709561+00:00
-- url     : https://prove2.me/theorems/fa48b425-8015-4d2c-b505-0419652c1041
-- title:
--   Global Theory: tensor Add Content smul
-- statement:
--   The Global Theory construction uses the tensor Add Content smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L963-L965
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L963-L965

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
open MvPolynomial Module
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)

theorem GlobalTheory.tensorAddContent_smul (f : MvPolynomial σ R) (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b (f • x) = gaussAddVal v f + tensorAddContent v b x := by sorry
