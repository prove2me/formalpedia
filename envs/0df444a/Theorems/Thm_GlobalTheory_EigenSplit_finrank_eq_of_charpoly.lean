-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_finrank_eq_of_charpoly
-- name    : GlobalTheory.EigenSplit.finrank_eq_of_charpoly
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:32.943814+00:00
-- url     : https://prove2.me/theorems/c153cdaa-f66f-4794-84ef-b69901e21c9d
-- title:
--   Eigen Split: finrank eq of charpoly
-- statement:
--   The Eigen Split construction uses the finrank eq of charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L588-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L588-L592

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
variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h

theorem GlobalTheory.EigenSplit.finrank_eq_of_charpoly [Nontrivial R] (hfree : ∀ i, Module.Free R (eigenSub ρ (σ i)))
    (r : ι → ℕ) (hr : ∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) (i : ι) :
    Module.finrank R (eigenSub ρ (σ i)) = r i := by sorry
