-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_eigenEquiv_symm_apply
-- name    : GlobalTheory.EigenSplit.eigenEquiv_symm_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:26.03858+00:00
-- url     : https://prove2.me/theorems/bc495355-13d5-4499-ae50-99d3a3013a5b
-- title:
--   Eigen Split: eigen Equiv symm apply
-- statement:
--   The Eigen Split construction uses the eigen Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L293-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L293-L295

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
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)

theorem GlobalTheory.EigenSplit.eigenEquiv_symm_apply [Fintype ι] (v : ∀ i, eigenSub ρ (σ i)) :
    (eigenEquiv h ρ).symm v = ∑ i, (v i : N) := by sorry
