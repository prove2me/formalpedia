-- Prove2me | Theorems.Thm_GlobalTheory_tensorAddContent_eq_of_basis
-- name    : GlobalTheory.tensorAddContent_eq_of_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:25.110816+00:00
-- url     : https://prove2.me/theorems/afebe99e-f71d-5567-80f6-8f4c310efdf6
-- title:
--   Global Theory: tensor Add Content eq of basis
-- statement:
--   The Global Theory construction uses the tensor Add Content eq of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L967-L969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L967-L969

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

theorem GlobalTheory.tensorAddContent_eq_of_basis (hv : ∀ a : O, 0 ≤ v (algebraMap O R a)) (c : Basis κ O M)
    (x : MvPolynomial σ R ⊗[O] M) : tensorAddContent v b x = tensorAddContent v c x := by sorry
