-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_iSup_measure_lt_exitTime
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.iSup_measure_lt_exitTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:57.302535+00:00
-- url     : https://prove2.me/theorems/cfe4f281-9f26-41ba-92da-767f1d9c0624
-- title:
--   MarkovProcess: iSup_measure_lt_exitTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The semigroup as the limit of its killed parts

Along an open exhaustion `U n ↑ α` of the state space, the killed kernels increase to the
transition kernels of the semigroup: for every time `t`, starting point `x` and measurable set
`B`,

  `⨆ n, killedKernel P hP (U n) _ t x B = P t x B`   (`iSup_killedKernel_apply`),

and the survival probabilities `Q x {t < τ_{U n}}` increase to one. This is the statement that the
whole-space semigroup is the minimal semigroup of its killed parts; it rests on the path-space
fact that exit times along an exhaustion tend to infinity (`Path/Exhaustion.lean`), so the
killed events increase to the whole event `{ω t ∈ B}`.

The killed kernels are monotone in the open set (`killedKernel_mono`); no other structure is
used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]







end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable [LocallyCompactSpace alpha]



end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The semigroup as the limit of its killed parts

Along an open exhaustion `U n ↑ α` of the state space, the killed kernels increase to the
transition kernels of the semigroup: for every time `t`, starting point `x` and measurable set
`B`,

  `⨆ n, killedKernel P hP (U n) _ t x B = P t x B`   (`iSup_killedKernel_apply`),

and the survival probabilities `Q x {t < τ_{U n}}` increase to one. This is the statement that the
whole-space semigroup is the minimal semigroup of its killed parts; it rests on the path-space
fact that exit times along an exhaustion tend to infinity (`Path/Exhaustion.lean`), so the
killed events increase to the whole event `{ω t ∈ B}`.

The killed kernels are monotone in the open set (`killedKernel_mono`); no other structure is
used.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.iSup_measure_lt_exitTime {U : ℕ → Set alpha}
    (hU : ContinuousPath.IsOpenExhaustion U) (t : NNReal) (x : alpha) :
    ⨆ n, IsConservative.continuousProcess P hP x
      {omega | (t : ℝ≥0∞) < ContinuousPath.exitTime (U n) omega} = 1 := by sorry
