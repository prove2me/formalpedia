-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_abs_log_div_le
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxChart.abs_log_div_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:06.580008+00:00
-- url     : https://prove2.me/theorems/52cdb74b-c1e6-59d2-81a2-c253fe484155
-- title:
--   Cx Chart: abs log div le
-- statement:
--   The Cx Chart construction uses the abs log div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MeasurableDomCellLogNormChart.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MeasurableDomCellLogNormChart.lean#L58-L63

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MeasurableDomCellLogNormChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxChart
open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.abs_log_div_le {t h c : ℝ} (ht : 0 ≤ t) (hh : 0 < h) (hc : |Real.log h| ≤ c) (hc0 : 0 ≤ c) :
    |Real.log (t / h)| ≤ |Real.log t| + c := by sorry
