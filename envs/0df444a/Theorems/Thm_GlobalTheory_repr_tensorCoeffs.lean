-- Prove2me | Theorems.Thm_GlobalTheory_repr_tensorCoeffs
-- name    : GlobalTheory.repr_tensorCoeffs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:16:07.384239+00:00
-- url     : https://prove2.me/theorems/377bfadd-95dc-47fe-a77d-670902beef2c
-- title:
--   Global Theory: repr tensor Coeffs
-- statement:
--   The Global Theory construction uses the repr tensor Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L847-L853
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L847-L853

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

theorem GlobalTheory.repr_tensorCoeffs (x : MvPolynomial σ R ⊗[O] M) (m : σ →₀ ℕ) (i : ι) :
    (b.baseChange R).repr (tensorCoeffs x m) i =
      coeff m ((b.baseChange (MvPolynomial σ R)).repr x i) := by sorry
