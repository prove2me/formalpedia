-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_IsEquivariant_eigenMap_exact
-- name    : GlobalTheory.EigenSplit.IsEquivariant.eigenMap_exact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:16.461797+00:00
-- url     : https://prove2.me/theorems/20950c46-d17a-4552-9b20-d855a9e64d23
-- title:
--   Is Equivariant: eigen Map exact
-- statement:
--   The Is Equivariant construction uses the eigen Map exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L331-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L331-L342

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
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h

theorem GlobalTheory.EigenSplit.IsEquivariant.eigenMap_exact {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''}
    (hf : IsEquivariant ρ ρ' f) (hg : IsEquivariant ρ' ρ'' g) (i : ι)
    (he : Function.Exact f g) :
    Function.Exact (hf.eigenMap (σ i)) (hg.eigenMap (σ i)) := by sorry
