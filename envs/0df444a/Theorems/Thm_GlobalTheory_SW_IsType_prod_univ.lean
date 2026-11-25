-- Prove2me | Theorems.Thm_GlobalTheory_SW_IsType_prod_univ
-- name    : GlobalTheory.SW.IsType.prod_univ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:25.98321+00:00
-- url     : https://prove2.me/theorems/a9db15e6-6bad-46db-b821-5a088ef624b8
-- title:
--   Is Type: prod univ
-- statement:
--   The Is Type construction uses the prod univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L52-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L52-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.IsType.prod_univ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {M : Type} [CommMonoid M] (g : (E →+* ℂ) → M) :
    ∏ σ, g σ = ∏ τ : Ψ, (g τ * g (ComplexEmbedding.conjugate τ.1)) := by sorry
