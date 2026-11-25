-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_of_basis
-- name    : GlobalTheory.EigenSplit.det_sq_eq_of_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:23.621838+00:00
-- url     : https://prove2.me/theorems/bc7668eb-1630-48f6-b769-6085f1f7e68c
-- title:
--   Eigen Split: det sq eq of basis
-- statement:
--   The Eigen Split construction uses the det sq eq of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L668-L681
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L668-L681

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

theorem GlobalTheory.EigenSplit.det_sq_eq_of_basis {O : Type*} [CommRing O] (σ : ι → O →+* R)
    (b b' : Module.Basis ι ℤ O) :
    (Matrix.of fun i j => σ i (b j)).det ^ 2 = (Matrix.of fun i j => σ i (b' j)).det ^ 2 := by sorry
