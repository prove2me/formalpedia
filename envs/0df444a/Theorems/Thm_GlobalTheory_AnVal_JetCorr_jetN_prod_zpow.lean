-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetCorr_jetN_prod_zpow
-- name    : GlobalTheory.AnVal.JetCorr.jetN_prod_zpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:52.547799+00:00
-- url     : https://prove2.me/theorems/740083f8-f135-4b9c-bb59-fecf701261b9
-- title:
--   Jet Corr: jet N prod zpow
-- statement:
--   The Jet Corr construction uses the jet N prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L91-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L91-L113

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

theorem GlobalTheory.AnVal.JetCorr.jetN_prod_zpow {n g : ℕ} (m : ℕ) {K : Type} [Fintype K] (f : K → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, AnalyticAt ℂ (f k) 0) (h0 : ∀ k, f k 0 ≠ 0)
    (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ) :
    ∃ u : K → (Jet ℂ (Fin n × Fin g) m)ˣ, (∀ k, (u k).val = jetN m fun w => f k (Λ k w)) ∧
      jetN m (fun w => ∏ k, f k (Λ k w) ^ ε k) = (∏ k, u k ^ ε k).val := by sorry
