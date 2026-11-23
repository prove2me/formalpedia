-- Prove2me | Theorems.Thm_GlobalTheory_tensorContent_eq_polyContent
-- name    : GlobalTheory.tensorContent_eq_polyContent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:01.479117+00:00
-- url     : https://prove2.me/theorems/6d384c5f-d0a7-49e3-afc9-9945c06b1661
-- title:
--   Global Theory: tensor Content eq poly Content
-- statement:
--   The Global Theory construction uses the tensor Content eq poly Content property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L855-L860
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L855-L860

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

theorem GlobalTheory.tensorContent_eq_polyContent (x : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b x = polyContent v (b.baseChange R) (tensorCoeffs x) := by sorry
