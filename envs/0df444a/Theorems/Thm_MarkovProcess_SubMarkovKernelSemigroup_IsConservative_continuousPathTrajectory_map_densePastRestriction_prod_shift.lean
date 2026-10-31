-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_densePastRestriction_prod_shift
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_densePastRestriction_prod_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:33:20.20506+00:00
-- url     : https://prove2.me/theorems/d46d2104-0fb0-4990-ad6c-f6c0bcd5c9d4
-- title:
--   MarkovProcess: continuousPathTrajectory_map_densePastRestriction_prod_shift
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_CompProdReindex_54ebfbc7
import Definitions.Def_MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
import Definitions.Def_MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestart_9d6a4f09
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
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
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The rational-time restart kernel and its joint law

This file merges the following former modules, one section each:

* `RationalJointKernel`: The rational past/future restart kernel
* `RationalRestartFiniteMarginals`: Finite marginals of the rational restart kernel
* `RationalJointLaw`: Rational-time joint restart law
-/

namespace MarkovProcess

section RationalJointKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]











end
end ContinuousPath

end RationalJointKernel

section RationalRestartFiniteMarginals

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal


noncomputable section

namespace MixedPastFuture









variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]













end MixedPastFuture

namespace SubMarkovKernelSemigroup.IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]









end SubMarkovKernelSemigroup.IsConservative
end

end RationalRestartFiniteMarginals

section RationalJointLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]



end
end IsConservative
end SubMarkovKernelSemigroup

end RationalJointLaw

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
# The rational-time restart kernel and its joint law

This file merges the following former modules, one section each:

* `RationalJointKernel`: The rational past/future restart kernel
* `RationalRestartFiniteMarginals`: Finite marginals of the rational restart kernel
* `RationalJointLaw`: Rational-time joint restart law
-/





open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_densePastRestriction_prod_shift
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) :
    (continuousPathTrajectory P hP default).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      ContinuousPath.rationalPastFutureRestartKernel
        (continuousPathTrajectory P hP default) S := by sorry
