-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedProcess_map_exitTime
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_exitTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:32:33.102009+00:00
-- url     : https://prove2.me/theorems/158a9bd9-6930-465e-8bda-8d73140c50b8
-- title:
--   MarkovProcess: killedProcess_map_exitTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Killed_Nested_fac741d0
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
# Nested domains: killing at the exit of a smaller set

For two sets `U ⊆ V` the path killed at the exit of `U` is the path killed at the exit of `V`,
killed once more at the exit of `U`.  This file proves that relation on path space and transports
it to the killed processes.

* `ContinuousPath.exitTime_mono`: a path leaves a smaller set no later;
* `LifetimePath.killedCoordinate W t`: the coordinate at time `t` of a lifetime path killed once
  more at the exit of `W`, together with its two coordinate formulas and its measurability for an
  open `W` (`LifetimePath.measurable_killedCoordinate`), which rests on the measurability of the
  lifetime-path exit time `LifetimePath.measurable_exitTime` proved here;
* `ContinuousPath.lifetimePath_exitTime_killAtExit`: the first time the `V`-killed path is not a
  live point of `U` is the exit time of `U`, that is, the lifetime of the `U`-killed path;
* `ContinuousPath.killedCoordinate_killAtExit`: killing the `V`-killed path once more at the exit
  of `U` reads, at every time, the coordinate of the `U`-killed path through the inclusion of `U`
  in `V`;
* `killedProcess_map_exitTime` and `killedProcess_map_killedCoordinates`: the same two statements
  for the laws, and finally `killedProcess_map_killedFinsetCoordinates`, the part-process property
  at the level of the finite-dimensional distributions: the process of `V` killed again at the
  exit of `U` has the finite-dimensional distributions of the cemetery extension of the killed
  semigroup on `U`.

The carriers of the two killed processes are the subtypes `U` and `V`, which are different types;
the statements here compare them through the inclusion of `U` in `V` rather than identifying the
two killed processes as laws on a common carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath

section Killing

variable {beta : Type*} [PseudoMetricSpace beta]







end Killing

section MeasurableExitTime

variable {beta : Type*} [PseudoMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]





end MeasurableExitTime

end LifetimePath

namespace ContinuousPath

section Nested

variable {alpha : Type*} [PseudoMetricSpace alpha] {U V : Set alpha}







end Nested

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U V : Set alpha)





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
# Nested domains: killing at the exit of a smaller set

For two sets `U ⊆ V` the path killed at the exit of `U` is the path killed at the exit of `V`,
killed once more at the exit of `U`.  This file proves that relation on path space and transports
it to the killed processes.

* `ContinuousPath.exitTime_mono`: a path leaves a smaller set no later;
* `LifetimePath.killedCoordinate W t`: the coordinate at time `t` of a lifetime path killed once
  more at the exit of `W`, together with its two coordinate formulas and its measurability for an
  open `W` (`LifetimePath.measurable_killedCoordinate`), which rests on the measurability of the
  lifetime-path exit time `LifetimePath.measurable_exitTime` proved here;
* `ContinuousPath.lifetimePath_exitTime_killAtExit`: the first time the `V`-killed path is not a
  live point of `U` is the exit time of `U`, that is, the lifetime of the `U`-killed path;
* `ContinuousPath.killedCoordinate_killAtExit`: killing the `V`-killed path once more at the exit
  of `U` reads, at every time, the coordinate of the `U`-killed path through the inclusion of `U`
  in `V`;
* `killedProcess_map_exitTime` and `killedProcess_map_killedCoordinates`: the same two statements
  for the laws, and finally `killedProcess_map_killedFinsetCoordinates`, the part-process property
  at the level of the finite-dimensional distributions: the process of `V` killed again at the
  exit of `U` has the finite-dimensional distributions of the cemetery extension of the killed
  semigroup on `U`.

The carriers of the two killed processes are the subtypes `U` and `V`, which are different types;
the statements here compare them through the inclusion of `U` in `V` rather than identifying the
two killed processes as laws on a common carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U V : Set alpha)

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_exitTime (hUV : U ⊆ V) (hU : IsOpen U) (hV : IsOpen V)
    (x : U) :
    (IsConservative.killedProcess P hP V hV (Set.inclusion hUV x)).map
        (LifetimePath.exitTime (Subtype.val ⁻¹' U : Set V)) =
      (IsConservative.killedProcess P hP U hU x).map LifetimePath.lifetime := by sorry
