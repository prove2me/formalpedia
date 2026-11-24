-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_baseChange_rTensor
-- name    : GlobalTheory.basisVal_baseChange_rTensor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:00.733775+00:00
-- url     : https://prove2.me/theorems/5ea8e4d0-dd47-489b-8a60-d5e4e2e980e4
-- title:
--   Global Theory: basis Val base Change r Tensor
-- statement:
--   The Global Theory construction uses the basis Val base Change r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L824-L833
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L824-L833

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

theorem GlobalTheory.basisVal_baseChange_rTensor (w : Valuation S Γ₀) (φ : R →ₐ[O] S)
    (h : ∀ a, w (φ a) = v a) (x : R ⊗[O] M) :
    basisVal w (b.baseChange S) (φ.toLinearMap.rTensor M x) = basisVal v (b.baseChange R) x := by sorry
