-- Prove2me | Theorems.Thm_GlobalTheory_AnValJetEx_jetOf_prod
-- name    : GlobalTheory.AnValJetEx.jetOf_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:18.46836+00:00
-- url     : https://prove2.me/theorems/e4e325b9-0ecf-5f0e-a646-c591ec9bca38
-- title:
--   An Val Jet Ex: jet Of prod
-- statement:
--   The An Val Jet Ex construction uses the jet Of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L114-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValJetEx.jetOf_prod {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by sorry
