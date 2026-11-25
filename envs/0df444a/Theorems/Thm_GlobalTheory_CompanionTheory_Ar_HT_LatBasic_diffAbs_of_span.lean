-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_diffAbs_of_span
-- name    : GlobalTheory.CompanionTheory.Ar.HT.LatBasic.diffAbs_of_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:35.478288+00:00
-- url     : https://prove2.me/theorems/69ded746-b05a-4d7e-b15b-91ea658a1939
-- title:
--   Lat Basic: diff Abs of span
-- statement:
--   The Lat Basic construction uses the diff Abs of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L364-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/LatNormGrLatNeZeroOfSpan.lean#L364-L370

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

theorem GlobalTheory.CompanionTheory.Ar.HT.LatBasic.diffAbs_of_span (v : Valuation K NNReal) (σ : E →+* K) {δ : 𝓞 E}
    (h : differentIdeal ℤ (𝓞 E) = Ideal.span {δ}) : diffAbs v σ = v (σ (δ : E)) := by sorry
