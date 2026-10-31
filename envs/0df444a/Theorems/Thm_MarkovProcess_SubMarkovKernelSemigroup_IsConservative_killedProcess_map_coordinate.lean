-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedProcess_map_coordinate
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_coordinate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:32:24.605087+00:00
-- url     : https://prove2.me/theorems/32a5a435-1bc6-413c-9d4e-629cc08ec05b
-- title:
--   MarkovProcess: killedProcess_map_coordinate
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_KillAtExit_9c0394fb
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath



end LifetimePath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

















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
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)















open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_coordinate (t : NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension (IsConservative.killedKernelOn P hP U hU t)
        (Cemetery.alive x) := by sorry
