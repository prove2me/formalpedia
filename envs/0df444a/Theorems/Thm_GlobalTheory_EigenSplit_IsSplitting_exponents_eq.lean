-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_IsSplitting_exponents_eq
-- name    : GlobalTheory.EigenSplit.IsSplitting.exponents_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:13.417019+00:00
-- url     : https://prove2.me/theorems/7724bc9b-df2e-4fd2-8d16-4e43a4be2741
-- title:
--   Is Splitting: exponents eq
-- statement:
--   The Is Splitting construction uses the exponents eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L554-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L554-L560

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

theorem GlobalTheory.EigenSplit.IsSplitting.exponents_eq [Nontrivial R] {σ : ι → O →+* R} (h : IsSplitting σ)
    (r s : ι → ℕ) (hrs : ∀ a, ∏ i, (X - C (σ i a)) ^ r i = ∏ i, (X - C (σ i a)) ^ s i) :
    r = s := by sorry
