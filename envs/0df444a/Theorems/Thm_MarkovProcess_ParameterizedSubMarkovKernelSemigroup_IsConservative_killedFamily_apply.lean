-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_IsConservative_killedFamily_apply
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.killedFamily_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:34:05.991053+00:00
-- url     : https://prove2.me/theorems/7ee90d53-d9eb-4444-a62e-03d65f824db3
-- title:
--   MarkovProcess: killedFamily_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Parameterized_Killed_7030495e
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
# The killed parameterized family

For a measurably parameterized family of conservative Feller semigroups and an open set `U`, the
processes of the fibres killed when they leave `U` again form a measurably parameterized family
of sub-Markov kernel semigroups on the carrier `U`: `killedFamily P hP U hU hFeller hK :
ParameterizedSubMarkovKernelSemigroup Theta U`, whose fibre at `theta` is the killed semigroup
`killedSemigroup` of `Killed/Semigroup.lean` for the semigroup at `theta`
(`killedFamily_toSubMarkovKernelSemigroup`, definitionally).  The only new content is the joint
measurability of the killed transition probabilities in the parameter, the time and the starting
point, `measurable_killedKernelOn_family`, which comes from the joint measurability of the
parameterized continuous-path process through the fibre identity.

The killed process on lifetime paths (with a cemetery state) is not constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]







end MarkovProcess.ParameterizedSubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The killed parameterized family

For a measurably parameterized family of conservative Feller semigroups and an open set `U`, the
processes of the fibres killed when they leave `U` again form a measurably parameterized family
of sub-Markov kernel semigroups on the carrier `U`: `killedFamily P hP U hU hFeller hK :
ParameterizedSubMarkovKernelSemigroup Theta U`, whose fibre at `theta` is the killed semigroup
`killedSemigroup` of `Killed/Semigroup.lean` for the semigroup at `theta`
(`killedFamily_toSubMarkovKernelSemigroup`, definitionally).  The only new content is the joint
measurability of the killed transition probabilities in the parameter, the time and the starting
point, `measurable_killedKernelOn_family`, which comes from the joint measurability of the
parameterized continuous-path process through the fibre identity.

The killed process on lifetime paths (with a cemetery state) is not constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]





open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.killedFamily_apply
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (theta : Theta) (t : NNReal) (x : U) {B : Set U}
    (hB : MeasurableSet B) :
    IsConservative.killedFamily P hP U hU hFeller hK theta t x B =
      IsConservative.continuousProcess P hP (theta, x)
        (ContinuousPath.killedEvent U t (Subtype.val '' B)) := by sorry
