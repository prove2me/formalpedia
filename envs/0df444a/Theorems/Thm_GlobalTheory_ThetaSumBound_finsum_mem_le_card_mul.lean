-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSumBound_finsum_mem_le_card_mul
-- name    : GlobalTheory.ThetaSumBound.finsum_mem_le_card_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:51.243431+00:00
-- url     : https://prove2.me/theorems/fb0ea00d-fd2b-43fb-859c-fc00e3efe08d
-- title:
--   Theta Sum Bound: finsum mem le card mul
-- statement:
--   The Theta Sum Bound construction uses the finsum mem le card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L14-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound

theorem GlobalTheory.ThetaSumBound.finsum_mem_le_card_mul {α ι : Type*} [Fintype ι] (g : ι → α) (S : Set α)
    (hS : S ⊆ Set.range g) (f : α → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a ∈ S, f a ≤ M) :
    ∑ᶠ (a : α) (_ : a ∈ S), f a ≤ Fintype.card ι * M := by sorry
