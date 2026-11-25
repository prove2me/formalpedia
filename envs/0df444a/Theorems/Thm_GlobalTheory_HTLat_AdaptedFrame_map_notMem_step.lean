-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_AdaptedFrame_map_notMem_step
-- name    : GlobalTheory.HTLat.AdaptedFrame.map_notMem_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:21.860513+00:00
-- url     : https://prove2.me/theorems/4f5a0b99-d9cc-49dd-83a8-1939a381d0d5
-- title:
--   Adapted Frame: map not Mem step
-- statement:
--   The Adapted Frame construction uses the map not Mem step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L532-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L532-L544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']

theorem GlobalTheory.HTLat.AdaptedFrame.map_notMem_step (al : U →ₗ[C] U') {U₁ : Submodule C U} {j : ℕ}
    (F : AdaptedFrame (LinearMap.ker al ⊓ U₁) U₁ N j) (i : Fin N) (hi : j ≤ i) :
    (al ∘ F.f) i ∉ step C (al ∘ F.f) i := by sorry
