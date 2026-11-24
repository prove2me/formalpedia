-- Prove2me | Theorems.Thm_GlobalTheory_basisVal_le_one_iff
-- name    : GlobalTheory.basisVal_le_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:02.101907+00:00
-- url     : https://prove2.me/theorems/ff678a3e-52e5-4404-8d92-2cd1969837b0
-- title:
--   Global Theory: basis Val le one iff
-- statement:
--   The Global Theory construction uses the basis Val le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L781-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L781-L795

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

theorem GlobalTheory.basisVal_le_one_iff (hO : v.Integers O) {x : M} :
    basisVal v b x ≤ 1 ↔ x ∈ Submodule.span O (Set.range b) := by sorry
