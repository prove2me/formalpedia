-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_iff_rankAtStalk_eq
-- name    : GlobalTheory.EigenSplit.charpoly_eq_iff_rankAtStalk_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:22.194437+00:00
-- url     : https://prove2.me/theorems/69a64b4e-9024-4686-8df0-56bbcea34a8c
-- title:
--   Eigen Split: charpoly eq iff rank At Stalk eq
-- statement:
--   The Eigen Split construction uses the charpoly eq iff rank At Stalk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L609-L632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L609-L632

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

theorem GlobalTheory.EigenSplit.charpoly_eq_iff_rankAtStalk_eq [Module.Free R N] [Module.Finite R N] (r : ι → ℕ) :
    (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
      ∀ (p : PrimeSpectrum R) i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i := by sorry
