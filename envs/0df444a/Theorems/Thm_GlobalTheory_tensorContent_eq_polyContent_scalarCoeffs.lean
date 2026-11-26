-- Prove2me | Theorems.Thm_GlobalTheory_tensorContent_eq_polyContent_scalarCoeffs
-- name    : GlobalTheory.tensorContent_eq_polyContent_scalarCoeffs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:30.73254+00:00
-- url     : https://prove2.me/theorems/238d564d-c27f-4a48-a814-3bd4f4fc8f15
-- title:
--   Global Theory: tensor Content eq poly Content scalar Coeffs
-- statement:
--   The Global Theory construction uses the tensor Content eq poly Content scalar Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L899-L910
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L899-L910

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

theorem GlobalTheory.tensorContent_eq_polyContent_scalarCoeffs {N : Type*} [AddCommGroup N] [Module R N]
    (c : Basis ι R N) (x : MvPolynomial σ R ⊗[R] N) :
    tensorContent v c x = polyContent v c (scalarCoeffs x) := by sorry
