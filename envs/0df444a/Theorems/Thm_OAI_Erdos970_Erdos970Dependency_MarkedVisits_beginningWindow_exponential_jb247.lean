-- Prove2me | Theorems.Thm_OAI_Erdos970_Erdos970Dependency_MarkedVisits_beginningWindow_exponential_jb247
-- name    : OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:02:22.506216+00:00
-- url     : https://prove2.me/theorems/6d74eb67-a912-4f22-a462-11193b2d8989
-- title:
--   OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential` of [lean/OAI/NumberTheory/Jacobsthal/Partitions/BeginningWindowTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/BeginningWindowTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.Erdos970Dependency.MarkedVisits`, with `open Filter Set MeasureTheory ProbabilityTheory`, `open scoped Topology ProbabilityTheory ENNReal`, `open NumberTheoryLean.KernelPotential`):
--
--   ```lean
--   theorem beginningWindow_exponential_jb247 : ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ z : RegCost, ∀ v H : ℝ,
--       0 < v → 0 ≤ H → beginningOvershoot z v H ≤ ENNReal.ofReal (C*Real.exp (-eta*H)) ∧
--         1-ENNReal.ofReal (C*Real.exp (-eta*H)) ≤ beginningWindowHit z v H
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.Erdos970Dependency.MarkedVisits.RegCost`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningOvershoot` and `OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindowHit` (definitions bundle `OAIQ247J008` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/BeginningWindowTransport.lean (declaration OAI.Erdos970.Erdos970Dependency.MarkedVisits.beginningWindow_exponential)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J008

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

theorem beginningWindow_exponential_jb247 : ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ z : RegCost, ∀ v H : ℝ,
    0 < v → 0 ≤ H → beginningOvershoot z v H ≤ ENNReal.ofReal (C*Real.exp (-eta*H)) ∧
      1-ENNReal.ofReal (C*Real.exp (-eta*H)) ≤ beginningWindowHit z v H := by
  sorry

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end
