-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isLocallyConstant_rankAtStalk_eigenSub
-- name    : GlobalTheory.EigenSplit.isLocallyConstant_rankAtStalk_eigenSub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:25.414365+00:00
-- url     : https://prove2.me/theorems/bf27019e-6b85-4b9f-99c8-30f77bce4d98
-- title:
--   Eigen Split: is Locally Constant rank At Stalk eigen Sub
-- statement:
--   The Eigen Split construction uses the is Locally Constant rank At Stalk eigen Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L636-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L636-L641

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
omit [Fintype ι]

theorem GlobalTheory.EigenSplit.isLocallyConstant_rankAtStalk_eigenSub [Module.Projective R N] [Module.Finite R N]
    (i : ι) : IsLocallyConstant (Module.rankAtStalk (R := R) (eigenSub ρ (σ i))) := by sorry
