-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isEquivariant_id
-- name    : GlobalTheory.EigenSplit.isEquivariant_id
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:22.818033+00:00
-- url     : https://prove2.me/theorems/beb4f524-d912-58eb-a6be-036427864873
-- title:
--   Eigen Split: is Equivariant id
-- statement:
--   The Eigen Split construction uses the is Equivariant id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L183-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L183-L184

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

theorem GlobalTheory.EigenSplit.isEquivariant_id (ρ : O →+* Module.End R N) : IsEquivariant ρ ρ LinearMap.id := by sorry
