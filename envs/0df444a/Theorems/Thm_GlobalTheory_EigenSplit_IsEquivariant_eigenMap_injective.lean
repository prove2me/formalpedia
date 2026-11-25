-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_IsEquivariant_eigenMap_injective
-- name    : GlobalTheory.EigenSplit.IsEquivariant.eigenMap_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:27.153631+00:00
-- url     : https://prove2.me/theorems/bfb0a513-a781-4f46-8555-3afb2419ee65
-- title:
--   Is Equivariant: eigen Map injective
-- statement:
--   The Is Equivariant construction uses the eigen Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L217-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L217-L220

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

theorem GlobalTheory.EigenSplit.IsEquivariant.eigenMap_injective {ρ : O →+* Module.End R N}
    {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R)
    (hi : Function.Injective f) : Function.Injective (hf.eigenMap χ) := by sorry
