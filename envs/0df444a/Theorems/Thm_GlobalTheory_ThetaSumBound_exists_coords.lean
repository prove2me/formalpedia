-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSumBound_exists_coords
-- name    : GlobalTheory.ThetaSumBound.exists_coords
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:30.687382+00:00
-- url     : https://prove2.me/theorems/377beaf9-cb43-4342-84e8-b7c395a38201
-- title:
--   Theta Sum Bound: exists coords
-- statement:
--   The Theta Sum Bound construction uses the exists coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L31-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L31-L55

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

theorem GlobalTheory.ThetaSumBound.exists_coords {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (hv : v ∈ ZSpan.fundamentalDomain b) (hL : ((5 : ℂ) ^ 2) • v ∈ lat b) :
    ∃ k : κ → Fin 25, ∑ i, (((k i : ℕ) : ℝ) / 25) • b i = v := by sorry
