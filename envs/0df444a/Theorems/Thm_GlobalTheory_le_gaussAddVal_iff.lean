-- Prove2me | Theorems.Thm_GlobalTheory_le_gaussAddVal_iff
-- name    : GlobalTheory.le_gaussAddVal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:42.202537+00:00
-- url     : https://prove2.me/theorems/0986d07f-5084-4844-91ae-5f5658851aee
-- title:
--   Global Theory: le gauss Add Val iff
-- statement:
--   The Global Theory construction uses the le gauss Add Val iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L497-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L497-L499

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

theorem GlobalTheory.le_gaussAddVal_iff {f : MvPolynomial σ R} {γ : Γ} :
    γ ≤ gaussAddVal v f ↔ ∀ m, γ ≤ v (coeff m f) := by sorry
