-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isClopen_setOf_rankAtStalk_eq
-- name    : GlobalTheory.EigenSplit.isClopen_setOf_rankAtStalk_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:12.663841+00:00
-- url     : https://prove2.me/theorems/4efc5ba1-346d-526b-9c3a-dde9d5c9419d
-- title:
--   Eigen Split: is Clopen set Of rank At Stalk eq
-- statement:
--   The Eigen Split construction uses the is Clopen set Of rank At Stalk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L643-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L643-L647

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
  {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
include h

theorem GlobalTheory.EigenSplit.isClopen_setOf_rankAtStalk_eq [Module.Projective R N] [Module.Finite R N] (r : ι → ℕ) :
    IsClopen {p : PrimeSpectrum R | ∀ i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i} := by sorry
