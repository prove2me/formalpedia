-- Prove2me | Theorems.Thm_GlobalTheory_T_chartSection_not_mem_components
-- name    : GlobalTheory.T.chartSection_not_mem_components
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:49.159892+00:00
-- url     : https://prove2.me/theorems/ad412d55-e04c-5586-8cf6-7d115420896b
-- title:
--   T: chart Section not mem components
-- statement:
--   The T construction uses the chart Section not mem components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ChartSectionNotMemComponentsStatement.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ChartSectionNotMemComponentsStatement.lean#L22-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChartSectionNotMemComponents
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
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChartSectionNotMemComponentsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.chartSection_not_mem_components : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by sorry
