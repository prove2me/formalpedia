-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_iff_isUnit_det
-- name    : GlobalTheory.EigenSplit.isSplitting_iff_isUnit_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:41.263323+00:00
-- url     : https://prove2.me/theorems/e2f41890-7cdc-4843-8baa-5ea83a9820c3
-- title:
--   Eigen Split: is Splitting iff is Unit det
-- statement:
--   The Eigen Split construction uses the is Splitting iff is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L128-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L128-L140

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
variable [DecidableEq ι]

theorem GlobalTheory.EigenSplit.isSplitting_iff_isUnit_det [Fintype ι] (σ : ι → O →+* R) (b : Module.Basis ι ℤ O) :
    IsSplitting σ ↔ IsUnit (Matrix.of fun i j => σ i (b j)).det := by sorry
