-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetCorr_jetOf_prod
-- name    : GlobalTheory.AnVal.JetCorr.jetOf_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:47.850487+00:00
-- url     : https://prove2.me/theorems/ee13b587-d593-578e-815e-213045499a6b
-- title:
--   Jet Corr: jet Of prod
-- statement:
--   The Jet Corr construction uses the jet Of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L77-L87

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
variable {N : ℕ} (m : ℕ)

theorem GlobalTheory.AnVal.JetCorr.jetOf_prod {K : Type} (s : Finset K) {F : K → (Fin N → ℂ) → ℂ} (hF : ∀ k, AnalyticAt ℂ (F k) 0) :
    jetOf m (fun v => ∏ k ∈ s, F k v) = ∏ k ∈ s, jetOf m (F k) := by sorry
