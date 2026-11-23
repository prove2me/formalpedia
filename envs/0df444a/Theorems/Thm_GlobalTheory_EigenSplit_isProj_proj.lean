-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isProj_proj
-- name    : GlobalTheory.EigenSplit.isProj_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:59.07781+00:00
-- url     : https://prove2.me/theorems/b4931e9f-0144-491d-b278-cd593b652f36
-- title:
--   Eigen Split: is Proj proj
-- statement:
--   The Eigen Split construction uses the is Proj proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L244-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L244-L245

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

theorem GlobalTheory.EigenSplit.isProj_proj (i : ι) : LinearMap.IsProj (eigenSub ρ (σ i)) (proj h ρ i) := by sorry
