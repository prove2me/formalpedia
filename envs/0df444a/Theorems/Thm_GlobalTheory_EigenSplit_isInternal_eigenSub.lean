-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isInternal_eigenSub
-- name    : GlobalTheory.EigenSplit.isInternal_eigenSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:15.450171+00:00
-- url     : https://prove2.me/theorems/54782408-5289-40b8-b37c-5547e37c6fbb
-- title:
--   Eigen Split: is Internal eigen Sub
-- statement:
--   The Eigen Split construction uses the is Internal eigen Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L299-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L299-L314

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
include h

theorem GlobalTheory.EigenSplit.isInternal_eigenSub [Finite ι] : DirectSum.IsInternal fun i => eigenSub ρ (σ i) := by sorry
