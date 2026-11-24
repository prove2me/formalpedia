-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_baseChange_one_tmul
-- name    : GlobalTheory.basisVal_baseChange_one_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:55.766106+00:00
-- url     : https://prove2.me/theorems/bbb22c89-3bb3-4fff-9185-3235879956d5
-- title:
--   Global Theory: basis Val base Change one tmul
-- statement:
--   The Global Theory construction uses the basis Val base Change one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L820-L822
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L820-L822

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
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)

theorem GlobalTheory.basisVal_baseChange_one_tmul (y : M) :
    basisVal v (b.baseChange R) (1 ⊗ₜ y) = basisVal (v.comap (algebraMap O R)) b y := by sorry
