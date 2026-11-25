-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_exists_smul_mem
-- name    : GlobalTheory.CompanionTheory.Ar.HT.LatBasic.exists_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:45.541671+00:00
-- url     : https://prove2.me/theorems/d699234e-75d9-559b-b6d9-0ba7ed0c6b79
-- title:
--   Lat Basic: exists smul mem
-- statement:
--   The Lat Basic construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L116-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L116-L137

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

theorem GlobalTheory.CompanionTheory.Ar.HT.LatBasic.exists_smul_mem (hv : v.Integers O) {L : Submodule O V} {x : V}
    (hx : x ∈ Submodule.span C (L : Set V)) : ∃ a : C, a ≠ 0 ∧ a • x ∈ L := by sorry
