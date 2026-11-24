-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_apply_mem_eigenSub
-- name    : GlobalTheory.EigenSplit.apply_mem_eigenSub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:13.200417+00:00
-- url     : https://prove2.me/theorems/411136f8-ebfb-4f36-bbd6-f13de8401a50
-- title:
--   Eigen Split: apply mem eigen Sub
-- statement:
--   The Eigen Split construction uses the apply mem eigen Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L157-L159

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

theorem GlobalTheory.EigenSplit.apply_mem_eigenSub {ρ : O →+* Module.End R N} {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) (a : O) : ρ a x ∈ eigenSub ρ χ := by sorry
