-- Prove2me | Theorems.Thm_GlobalTheory_T_integrable_domCell_logNorm_chart
-- name    : GlobalTheory.T.integrable_domCell_logNorm_chart
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:14.039264+00:00
-- url     : https://prove2.me/theorems/f3c6c704-4b7a-4657-a3d9-3a764a97ad6e
-- title:
--   T: integrable dom Cell log Norm chart
-- statement:
--   The T construction uses the integrable dom Cell log Norm chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MeasurableDomCellLogNormChartStatement.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MeasurableDomCellLogNormChartStatement.lean#L22-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MeasurableDomCellLogNormChart
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
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MeasurableDomCellLogNormChartStatement
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

theorem GlobalTheory.T.integrable_domCell_logNorm_chart : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by sorry
