-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod_of_isLocalRing
-- name    : GlobalTheory.EigenSplit.charpoly_eq_prod_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:27.49987+00:00
-- url     : https://prove2.me/theorems/64da877f-1270-43ac-9304-bbf0f1b21558
-- title:
--   Eigen Split: charpoly eq prod of is Local Ring
-- statement:
--   The Eigen Split construction uses the charpoly eq prod of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L584-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L584-L586

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

theorem GlobalTheory.EigenSplit.charpoly_eq_prod_of_isLocalRing [IsLocalRing R] (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i)) := by sorry
