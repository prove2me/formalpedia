-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_eigProj_of_mem
-- name    : GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:36.772455+00:00
-- url     : https://prove2.me/theorems/fe121db3-14c0-5aed-8f40-eb4bb49d1f6b
-- title:
--   Lat Basic: eig Proj of mem
-- statement:
--   The Lat Basic construction uses the eig Proj of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L274-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L274-L282

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
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_of_mem {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} (hx : x ∈ eigSp ρ σ) :
    eigProj ρ σ x = x := by sorry
