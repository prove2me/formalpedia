-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_mem_latIn
-- name    : GlobalTheory.CompanionTheory.Ar.HT.LatBasic.mem_latIn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:48.915367+00:00
-- url     : https://prove2.me/theorems/88d7cfa4-5e29-4693-ae07-7d8ad1b87f73
-- title:
--   Lat Basic: mem lat In
-- statement:
--   The Lat Basic construction uses the mem lat In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L81-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

theorem GlobalTheory.CompanionTheory.Ar.HT.LatBasic.mem_latIn {L : Submodule O V} {U : Submodule C V} {x : U} :
    x ∈ latIn L U ↔ (x : V) ∈ L := by sorry
