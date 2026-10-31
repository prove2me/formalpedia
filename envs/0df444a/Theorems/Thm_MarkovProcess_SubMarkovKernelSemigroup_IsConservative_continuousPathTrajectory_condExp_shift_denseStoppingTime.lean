-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_condExp_shift_denseStoppingTime
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_condExp_shift_denseStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:32:27.044647+00:00
-- url     : https://prove2.me/theorems/b44320b1-0a42-47ef-ba67-b026815a7319
-- title:
--   MarkovProcess: continuousPathTrajectory_condExp_shift_denseStoppingTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Trajectory_RationalConditional_eedb6623
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional restart at dense-time-valued stopping times

This file specializes the countable-range stopping-time restart theorem to stopping times valued
in `DenseTime`.  The associated physical stopping time is obtained through
`DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
proved only at physical times attained by that range.

The result is a conditional-expectation identity for the canonical continuous trajectory at
dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha E : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional restart at dense-time-valued stopping times

This file specializes the countable-range stopping-time restart theorem to stopping times valued
in `DenseTime`.  The associated physical stopping time is obtained through
`DenseTime.castOrderEmbedding`; its range is countable, and deterministic restart is required and
proved only at physical times attained by that range.

The result is a conditional-expectation identity for the canonical continuous trajectory at
dense-time-valued stopping times.  An arbitrary finite `NNReal`-valued stopping time is covered
in `Trajectory/FellerStoppingConditional.lean`, and a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha E : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_condExp_shift_denseStoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (tau : ContinuousPath alpha → DenseTime)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦
        ((DenseTime.castOrderEmbedding (tau omega) : NNReal) : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (DenseTime.castOrderEmbedding (tau omega)) omega)|
      htau.measurableSpace] =ᵐ[(continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (DenseTime.castOrderEmbedding (tau omega))) := by sorry
