-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_finiteDenseApproximationOrderedTimes_apply
-- name    : MarkovProcess.SubMarkovKernelSemigroup.finiteDenseApproximationOrderedTimes_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:19.766078+00:00
-- url     : https://prove2.me/theorems/4c3b69f6-3991-4956-b465-4f63dde11f19
-- title:
--   MarkovProcess: finiteDenseApproximationOrderedTimes_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_FiniteDenseApproximationOrdered_4fc0c4f5
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

















end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal





open MarkovProcess.SubMarkovKernelSemigroup in
@[simp]

theorem MarkovProcess.SubMarkovKernelSemigroup.finiteDenseApproximationOrderedTimes_apply {I : Finset NNReal}
    (q : I ↪o DenseTime) (i : Fin I.card) :
    finiteDenseApproximationOrderedTimes q i =
      DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)) := by sorry
