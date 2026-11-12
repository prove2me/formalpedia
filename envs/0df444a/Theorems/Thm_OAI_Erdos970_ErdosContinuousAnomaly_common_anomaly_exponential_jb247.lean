-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosContinuousAnomaly_common_anomaly_exponential_jb247
-- name    : OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:53:50.853083+00:00
-- url     : https://prove2.me/theorems/15e7a70e-9fa4-41b6-8b62-b716e4e03bf3
-- title:
--   OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential` of [lean/OAI/NumberTheory/Jacobsthal/Harmonic/WeightedAnomalyConvergence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Harmonic/WeightedAnomalyConvergence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosContinuousAnomaly`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.Filter _root_.Erdos970.Set _root_.Erdos970.Filter`, `open scoped Topology`, `open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BoundaryAnomaly`):
--
--   ```lean
--   theorem common_anomaly_exponential_jb247 : ∃ C c w₀ : ℝ,0 < C ∧ 0 < c ∧ 1 < w₀ ∧
--       (∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
--         |anomaly w i r| ≤ C*Real.exp (-c*r)) ∧
--       (∀ r : ℝ,2 ≤ r → ∀ i : Side,
--         |continuousAnomaly i r| ≤ C*Real.exp (-c*r))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Side` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.ErdosContinuousAnomaly.continuousAnomaly` and `OAI.Erdos970.NumberTheoryLean.BoundaryAnomaly.anomaly` (definitions bundle `OAIQ247J007` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_first_loss_eq_one_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_loss_summable_jb247`, `OAI.Erdos970.ErdosContinuousOmission.actual_signed_loss_series_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.compact_limiting_integral_tendsto_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.floored_source_correction_tendsto_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.fullWeighted_section_radial_jb247`, `OAI_Erdos970_ErdosCorrectionLimit_full_continuous_correction_limit_jb247`, `OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247`, `OAI_Erdos970_ErdosCorrectionLimit_full_limiting_integral_fubini_jb247`, `OAI_Erdos970_ErdosOmissionBindings_actual_third_loss_eq_L3_jb247`, `OAI.Erdos970.ErdosOmissionBindings.second_loss_bounded_jb247`, `OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_loss_le_scalarTailMass_jb247`, `OAI_Erdos970_ErdosOmissionTail_actual_omission_tail_lt_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integrable_jb247`, `OAI.Erdos970.ErdosOmissionTail.combinedDensity_integral_jb247` and `OAI_Erdos970_ErdosSourceReferenceMargin_actual_sourceReference_tendsto_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Harmonic/WeightedAnomalyConvergence.lean (declaration OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J007

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BoundaryAnomaly

theorem common_anomaly_exponential_jb247 : ∃ C c w₀ : ℝ,0 < C ∧ 0 < c ∧ 1 < w₀ ∧
    (∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-c*r)) ∧
    (∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |continuousAnomaly i r| ≤ C*Real.exp (-c*r)) := by
  sorry

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end
