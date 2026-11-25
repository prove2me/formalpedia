-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_mem_eigSubLat
-- name    : GlobalTheory.HTLat.mem_eigSubLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:50.410971+00:00
-- url     : https://prove2.me/theorems/3b269f35-3d6f-422b-bc6c-e0b5f9f095bb
-- title:
--   HTLat: mem eig Sub Lat
-- statement:
--   The HTLat construction uses the mem eig Sub Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L27-L28

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

theorem GlobalTheory.HTLat.mem_eigSubLat {χ : Λ →+* C} {X : Submodule O V} {x : V} :
    x ∈ eigSubLat ρ χ X ↔ x ∈ X ∧ x ∈ eigenSub ρ χ := by sorry
