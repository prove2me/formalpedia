-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_algHom_le
-- name    : GlobalTheory.gaussVal_algHom_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:27.49017+00:00
-- url     : https://prove2.me/theorems/8884e88c-f448-46e6-a054-8425628f9095
-- title:
--   Global Theory: gauss Val alg Hom le
-- statement:
--   The Global Theory construction uses the gauss Val alg Hom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L279-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L279-L283

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

theorem GlobalTheory.gaussVal_algHom_le (e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (f : MvPolynomial σ R) :
    gaussVal v (e f) ≤ gaussVal v f := by sorry
