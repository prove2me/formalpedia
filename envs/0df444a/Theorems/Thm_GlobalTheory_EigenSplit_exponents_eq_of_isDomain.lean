-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_exponents_eq_of_isDomain
-- name    : GlobalTheory.EigenSplit.exponents_eq_of_isDomain
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:49.057644+00:00
-- url     : https://prove2.me/theorems/f4d963a0-78b0-447e-8bda-9c16026c3ec1
-- title:
--   Eigen Split: exponents eq of is Domain
-- statement:
--   The Eigen Split construction uses the exponents eq of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L492-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L492-L552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]

theorem GlobalTheory.EigenSplit.exponents_eq_of_isDomain [IsDomain R] {σ : ι → O →+* R} (hσ : Function.Injective σ)
    (r s : ι → ℕ) (hrs : ∀ a, ∏ i, (X - C (σ i a)) ^ r i = ∏ i, (X - C (σ i a)) ^ s i) :
    r = s := by sorry
