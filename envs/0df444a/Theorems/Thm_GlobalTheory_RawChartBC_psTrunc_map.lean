-- Prove2me | Theorems.Thm_GlobalTheory_RawChartBC_psTrunc_map
-- name    : GlobalTheory.RawChartBC.psTrunc_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:15:37.544555+00:00
-- url     : https://prove2.me/theorems/7e08f28a-a9dd-4ca1-b8bc-8c128d8389a0
-- title:
--   Raw Chart BC: ps Trunc map
-- statement:
--   The Raw Chart BC construction uses the ps Trunc map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L33-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem GlobalTheory.RawChartBC.psTrunc_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (f : MvPowerSeries κ S) :
    psTrunc m (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psTrunc m f) := by sorry
