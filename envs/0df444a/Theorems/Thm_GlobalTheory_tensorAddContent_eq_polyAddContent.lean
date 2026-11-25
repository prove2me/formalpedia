-- Prove2me | Theorems.Thm_GlobalTheory_tensorAddContent_eq_polyAddContent
-- name    : GlobalTheory.tensorAddContent_eq_polyAddContent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:30.77431+00:00
-- url     : https://prove2.me/theorems/40067f34-3133-5f3a-b03f-f030a925b9fa
-- title:
--   Global Theory: tensor Add Content eq poly Add Content
-- statement:
--   The Global Theory construction uses the tensor Add Content eq poly Add Content property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L959-L961
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L959-L961

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

theorem GlobalTheory.tensorAddContent_eq_polyAddContent (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b x = polyAddContent v (b.baseChange R) (tensorCoeffs x) := by sorry
