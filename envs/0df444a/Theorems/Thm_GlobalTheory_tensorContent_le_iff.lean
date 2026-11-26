-- Prove2me | Theorems.Thm_GlobalTheory_tensorContent_le_iff
-- name    : GlobalTheory.tensorContent_le_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:28.096532+00:00
-- url     : https://prove2.me/theorems/5ca80526-ba2a-5d54-b111-6b36043f8797
-- title:
--   Global Theory: tensor Content le iff
-- statement:
--   The Global Theory construction uses the tensor Content le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L862-L864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L862-L864

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

theorem GlobalTheory.tensorContent_le_iff {x : MvPolynomial σ R ⊗[O] M} {γ : Γ₀} :
    tensorContent v b x ≤ γ ↔ ∀ m, basisVal v (b.baseChange R) (tensorCoeffs x m) ≤ γ := by sorry
