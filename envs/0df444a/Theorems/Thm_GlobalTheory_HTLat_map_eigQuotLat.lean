-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_map_eigQuotLat
-- name    : GlobalTheory.HTLat.map_eigQuotLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:25.437002+00:00
-- url     : https://prove2.me/theorems/e03bd3a5-f8b4-4aad-a6e5-2695b6604315
-- title:
--   HTLat: map eig Quot Lat
-- statement:
--   The HTLat construction uses the map eig Quot Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L63-L71

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

theorem GlobalTheory.HTLat.map_eigQuotLat {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V'] [IsScalarTower O C V']
    {ρ' : Λ →+* Module.End C V'} {f : V →ₗ[C] V'} (hf : IsEquivariant ρ ρ' f) (i : ι)
    (X : Submodule O V) :
    (eigQuotLat ρ h i X).map (f.restrictScalars O) =
      eigQuotLat ρ' h i (X.map (f.restrictScalars O)) := by sorry
