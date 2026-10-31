-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_restrict_map_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:31:05.014871+00:00
-- url     : https://prove2.me/theorems/a9691b47-1357-45e1-8c0c-9a814c857a12
-- title:
--   MarkovProcess: continuousPathTrajectory_restrict_map_shift
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
import Definitions.Def_MarkovProcess_V3H_Path_MeasureIdentification_8dc880ce
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeApproximationFromAbove_7f339f12
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
import Definitions.Def_MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/


/-!
# Event-restricted deterministic restart for the Feller trajectory

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the deterministic-time canonical filtration. The proof approaches the
time strictly from above by dense times, identifies every finite dense future marginal by compact
tests, and then uses measure identification on dense restrictions.

The time here is deterministic. The strong Markov property at a finite stopping time is in
`Trajectory/FellerStoppingRestart.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]







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
# Event-restricted deterministic restart for the Feller trajectory

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the deterministic-time canonical filtration. The proof approaches the
time strictly from above by dense times, identifies every finite dense future marginal by compact
tests, and then uses measure identification on dense restrictions.

The time here is deterministic. The strong Markov property at a finite stopping time is in
`Trajectory/FellerStoppingRestart.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_restrict_map_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (s : NNReal) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A →
        ((((continuousPathTrajectory P hP default) x).restrict A).map
            (ContinuousPath.shift s)) =
          Kernel.comap (continuousPathTrajectory P hP default)
              (ContinuousPath.coordinateProcess (alpha := alpha) s)
              (ContinuousPath.measurable_coordinateProcess s) ∘ₘ
            (((continuousPathTrajectory P hP default) x).restrict A) := by sorry
