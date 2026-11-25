-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isUnit_discr_of_isSplitting
-- name    : GlobalTheory.EigenSplit.isUnit_discr_of_isSplitting
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:19.790566+00:00
-- url     : https://prove2.me/theorems/4fad32e7-552f-4165-8ecf-4a5a2e1b6687
-- title:
--   Eigen Split: is Unit discr of is Splitting
-- statement:
--   The Eigen Split construction uses the is Unit discr of is Splitting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L770-L773
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L770-L773

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
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.EigenSplit.isUnit_discr_of_isSplitting {σ : ι → 𝓞 E →+* R} (b : Module.Basis ι ℤ (𝓞 E))
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    (h : IsSplitting σ) : IsUnit (NumberField.discr E : R) := by sorry
