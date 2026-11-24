-- Prove2me | Theorems.Thm_GlobalTheory_basisAddVal_smul
-- name    : GlobalTheory.basisAddVal_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:46.987382+00:00
-- url     : https://prove2.me/theorems/939ffd87-ac8f-4371-9c19-596619449ffa
-- title:
--   Global Theory: basis Add Val smul
-- statement:
--   The Global Theory construction uses the basis Add Val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L936-L938
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L936-L938

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
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)

theorem GlobalTheory.basisAddVal_smul (a : R) (x : M) :
    basisAddVal v b (a • x) = v a + basisAddVal v b x := by sorry
