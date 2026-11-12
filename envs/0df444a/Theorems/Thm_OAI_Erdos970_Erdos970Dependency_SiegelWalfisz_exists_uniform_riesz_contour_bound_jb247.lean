-- Prove2me | Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_uniform_riesz_contour_bound_jb247
-- name    : OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:54:38.233745+00:00
-- url     : https://prove2.me/theorems/9fa9211d-b431-40cc-ace0-a303257d6549
-- title:
--   OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound` of [lean/OAI/NumberTheory/Jacobsthal/Estimates/RecoveryScale.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/RecoveryScale.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.Complex _root_.MeasureTheory`):
--
--   ```lean
--   theorem exists_uniform_riesz_contour_bound_jb247 :
--       ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
--         ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
--         ∀ X sigma T : ℝ, 1 ≤ X → 1 < sigma → sigma ≤ 2 → 0 < T →
--         ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
--           (1/(2*Real.pi)) *
--             (4*Real.pi*C*(modulusHeight q T)^3*X^(rieszContourLeft a q T) +
--               16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) +
--               8*((sigma-1)⁻¹+B)*X^sigma/T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight` (definitions bundle `OAIQ247J002` of this split); `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszSum` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.rieszContourLeft` (definitions bundle `OAIQ247J007` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247`, `OAI.Erdos970.ErdosStoppedTagSieve.finite_tag_sieve_error_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_intersection_prime_error_jb247`, `OAI_Erdos970_ErdosStoppedTagSieve_moving_subbin_prime_lower_jb247` and `OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/RecoveryScale.lean (declaration OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_uniform_riesz_contour_bound)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J007

section

attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory

theorem exists_uniform_riesz_contour_bound_jb247 :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ X sigma T : ℝ, 1 ≤ X → 1 < sigma → sigma ≤ 2 → 0 < T →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        (1/(2*Real.pi)) *
          (4*Real.pi*C*(modulusHeight q T)^3*X^(rieszContourLeft a q T) +
            16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) +
            8*((sigma-1)⁻¹+B)*X^sigma/T) := by
  sorry

end Erdos970Dependency.SiegelWalfisz

end Erdos970

end OAI
end
