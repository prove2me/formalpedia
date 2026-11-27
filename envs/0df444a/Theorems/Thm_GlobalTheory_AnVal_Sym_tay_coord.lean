-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_Sym_tay_coord
-- name    : GlobalTheory.AnVal.Sym.tay_coord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:02.288842+00:00
-- url     : https://prove2.me/theorems/ad0243a9-d94a-5d36-ba2a-219f66e066c2
-- title:
--   Sym: tay coord
-- statement:
--   The Sym construction uses the tay coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSymmetryTrivial.lean#L19-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSymmetryTrivial.lean#L19-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSymmetryTrivial
import Theorems.Thm_GlobalTheory_JetLinSub_tay_coord

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
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.Sym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.Sym.tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by sorry
