-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetCorr_prod_zpow_fiber
-- name    : GlobalTheory.AnVal.JetCorr.prod_zpow_fiber
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:43:59.071056+00:00
-- url     : https://prove2.me/theorems/f233aa8c-5e64-43b8-b2da-9c57b68982d4
-- title:
--   Jet Corr: prod zpow fiber
-- statement:
--   The Jet Corr construction uses the prod zpow fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L116-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L116-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetCorr
open scoped Classical

theorem GlobalTheory.AnVal.JetCorr.prod_zpow_fiber {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by sorry
