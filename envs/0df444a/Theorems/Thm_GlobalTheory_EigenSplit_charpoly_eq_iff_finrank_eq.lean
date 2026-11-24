-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_iff_finrank_eq
-- name    : GlobalTheory.EigenSplit.charpoly_eq_iff_finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:31.67367+00:00
-- url     : https://prove2.me/theorems/6c085ba3-4120-43d3-a117-d17bc0fe96e3
-- title:
--   Eigen Split: charpoly eq iff finrank eq
-- statement:
--   The Eigen Split construction uses the charpoly eq iff finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L594-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L594-L598

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

theorem GlobalTheory.EigenSplit.charpoly_eq_iff_finrank_eq [IsLocalRing R] (r : ι → ℕ) :
    (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
      ∀ i, Module.finrank R (eigenSub ρ (σ i)) = r i := by sorry
