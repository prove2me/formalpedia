-- Prove2me | Theorems.Thm_GlobalTheory_T_domCell_logNorm_measurable_invariant
-- name    : GlobalTheory.T.domCell_logNorm_measurable_invariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:29:34.354108+00:00
-- url     : https://prove2.me/theorems/9eac5cb8-9482-50a4-ae88-aec37141551e
-- title:
--   T: dom Cell log Norm measurable invariant
-- statement:
--   The T construction uses the dom Cell log Norm measurable invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/DomCellLogNormMeasurableInvariantStatement.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/DomCellLogNormMeasurableInvariantStatement.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_DomCellLogNormMeasurableInvariant
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
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_DomCellLogNormMeasurableInvariantStatement
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

theorem GlobalTheory.T.domCell_logNorm_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by sorry
