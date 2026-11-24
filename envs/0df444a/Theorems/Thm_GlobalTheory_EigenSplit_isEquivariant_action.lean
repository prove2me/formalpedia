-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isEquivariant_action
-- name    : GlobalTheory.EigenSplit.isEquivariant_action
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:30.579303+00:00
-- url     : https://prove2.me/theorems/df3f09b6-eec4-4762-92d9-264925c7a013
-- title:
--   Eigen Split: is Equivariant action
-- statement:
--   The Eigen Split construction uses the is Equivariant action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L186-L188

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

theorem GlobalTheory.EigenSplit.isEquivariant_action (ρ : O →+* Module.End R N) (c : O) : IsEquivariant ρ ρ (ρ c) := by sorry
