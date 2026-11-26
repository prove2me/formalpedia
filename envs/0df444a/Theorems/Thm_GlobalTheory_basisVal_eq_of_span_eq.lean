-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_eq_of_span_eq
-- name    : GlobalTheory.basisVal_eq_of_span_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:40.639789+00:00
-- url     : https://prove2.me/theorems/5f068ec6-8fdd-4eed-ba3a-d7d4aa5e63ca
-- title:
--   Global Theory: basis Val eq of span eq
-- statement:
--   The Global Theory construction uses the basis Val eq of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L797-L802
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L797-L802

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
open Module
variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]

theorem GlobalTheory.basisVal_eq_of_span_eq (hO : v.Integers O) (c : Basis κ R M)
    (h : Submodule.span O (Set.range b) = Submodule.span O (Set.range c)) (x : M) :
    basisVal v b x = basisVal v c x := by sorry
