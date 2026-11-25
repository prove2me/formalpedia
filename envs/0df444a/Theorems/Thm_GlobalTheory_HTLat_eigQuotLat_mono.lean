-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_eigQuotLat_mono
-- name    : GlobalTheory.HTLat.eigQuotLat_mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:10.507808+00:00
-- url     : https://prove2.me/theorems/87c3621f-1b17-40ab-aa71-19fb79483443
-- title:
--   HTLat: eig Quot Lat mono
-- statement:
--   The HTLat construction uses the eig Quot Lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L60-L61

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
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Λ : Type} [CommRing Λ] (ρ : Λ →+* Module.End C V)
variable {ι : Type} [DecidableEq ι] {σ : ι → Λ →+* C} (h : IsSplitting σ)

theorem GlobalTheory.HTLat.eigQuotLat_mono (i : ι) {X Y : Submodule O V} (hXY : X ≤ Y) :
    eigQuotLat ρ h i X ≤ eigQuotLat ρ h i Y := by sorry
