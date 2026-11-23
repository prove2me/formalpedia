-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod
-- name    : GlobalTheory.EigenSplit.charpoly_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:50.855802+00:00
-- url     : https://prove2.me/theorems/a26f4dc2-e01b-44f6-b55c-2d58864939d9
-- title:
--   Eigen Split: charpoly eq prod
-- statement:
--   The Eigen Split construction uses the charpoly eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L566-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L566-L582

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

theorem GlobalTheory.EigenSplit.charpoly_eq_prod (hfree : ∀ i, Module.Free R (eigenSub ρ (σ i))) (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i)) := by sorry
