-- Prove2me | Theorems.Thm_GlobalTheory_tensorContent_eq_of_basis
-- name    : GlobalTheory.tensorContent_eq_of_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:10.177831+00:00
-- url     : https://prove2.me/theorems/44fc5c06-6581-45bf-98f7-695a88b521fc
-- title:
--   Global Theory: tensor Content eq of basis
-- statement:
--   The Global Theory construction uses the tensor Content eq of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L886-L888
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L886-L888

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

theorem GlobalTheory.tensorContent_eq_of_basis (hv : ∀ a : O, v (algebraMap O R a) ≤ 1) (c : Basis κ O M)
    (x : MvPolynomial σ R ⊗[O] M) : tensorContent v b x = tensorContent v c x := by sorry
