-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetUniq_fderiv_comp_lin
-- name    : GlobalTheory.AnVal.JetUniq.fderiv_comp_lin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:01.066887+00:00
-- url     : https://prove2.me/theorems/61371ac2-5af4-54d1-9c2c-7ca3e37bad7b
-- title:
--   Jet Uniq: fderiv comp lin
-- statement:
--   The Jet Uniq construction uses the fderiv comp lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FderivEqOfJetOf.lean#L224-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FderivEqOfJetOf.lean#L224-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq

theorem GlobalTheory.AnVal.JetUniq.fderiv_comp_lin {a b : ℕ} (θ : (Fin b → ℂ) → ℂ) (hθ : DifferentiableAt ℂ θ 0)
    (T : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (v : Fin a → ℂ) :
    fderiv ℂ (fun z => θ (T z)) 0 v = fderiv ℂ θ 0 (T v) := by sorry
