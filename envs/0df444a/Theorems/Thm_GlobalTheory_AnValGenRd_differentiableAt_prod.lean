-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenRd_differentiableAt_prod
-- name    : GlobalTheory.AnValGenRd.differentiableAt_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:41.730229+00:00
-- url     : https://prove2.me/theorems/f61dd884-b83f-531a-98b5-5faa1995e573
-- title:
--   An Val Gen Rd: differentiable At prod
-- statement:
--   The An Val Gen Rd construction uses the differentiable At prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L18-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
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
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValGenRd.differentiableAt_prod {E K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset K)
    (f : K → E → ℂ) (z : E) (h : ∀ k, DifferentiableAt ℂ (f k) z) :
    DifferentiableAt ℂ (fun w => ∏ k ∈ s, f k w) z := by sorry
