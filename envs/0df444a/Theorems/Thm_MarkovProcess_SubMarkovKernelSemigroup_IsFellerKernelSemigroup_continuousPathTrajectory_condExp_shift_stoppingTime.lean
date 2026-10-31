-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_condExp_shift_stoppingTime
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_stoppingTime
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:32:34.659768+00:00
-- url     : https://prove2.me/theorems/2a346d99-f8e4-4c65-92f2-f8f6aab3f4ef
-- title:
--   MarkovProcess: continuousPathTrajectory_condExp_shift_stoppingTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Definitions.Def_MarkovProcess_V3H_Trajectory_DenseRestrictionMarginals_931e4c17
import Definitions.Def_MarkovProcess_V3H_Trajectory_FellerRestrictedRestart_8026f3b2
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
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
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
# Conditional expectation of the Feller trajectory at finite stopping times

For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
expectation of a bounded strongly measurable functional of the shifted canonical Feller
trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
into the generic conditional-expectation bridge; measurability of the restarted expectation for
the stopped sigma-algebra comes from progressive measurability of the coordinate process.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



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
# Conditional expectation of the Feller trajectory at finite stopping times

For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
expectation of a bounded strongly measurable functional of the shifted canonical Feller
trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
into the generic conditional-expectation bridge; measurability of the restarted expectation for
the stopped sigma-algebra comes from progressive measurability of the coordinate process.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_stoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (T omega)) := by sorry
