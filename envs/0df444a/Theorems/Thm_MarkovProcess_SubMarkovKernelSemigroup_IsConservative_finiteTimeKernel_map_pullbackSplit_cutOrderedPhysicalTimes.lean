-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:56.403594+00:00
-- url     : https://prove2.me/theorems/3389d69f-271f-43c1-86cd-ba50785e8f88
-- title:
--   MarkovProcess: finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelMixedPullback_8cf93300
import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
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
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
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
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory


noncomputable section

namespace MixedPastFuture



































variable {alpha : Type*} [MeasurableSpace alpha]



end MixedPastFuture

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]











variable [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



end ContinuousPath
end

end MixedPastFutureCoordinates

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MixedPastFuture

noncomputable section











































































variable {alpha : Type*}





variable [MeasurableSpace alpha]



















end
end MixedPastFuture

namespace SubMarkovKernelSemigroup
namespace IsConservative





end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutCoordinates

section MixedPastFutureCutFactorization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace SubMarkovKernelSemigroup
namespace IsConservative



end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutFactorization

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
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a rational cut
-/




open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory





open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
    {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (pastIndex : pastLabel → Fin (MixedPastFuture.pastPredecessorCard S I + 1))
    (futureIndex : futureLabel →
      Option (Fin (MixedPastFuture.positiveFutureFinset S I).card)) :
    (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
      (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex ∘
          MarkovProcess.SubMarkovKernelSemigroup.splitFinitePath
            (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I)
            (n := (MixedPastFuture.positiveFutureFinset S I).card)) =
      (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.cutPastOrderedPhysicalTimes S I) ⊗ₖ
        (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (MarkovProcess.SubMarkovKernelSemigroup.splitPastTerminal
              (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            MarkovProcess.SubMarkovKernelSemigroup.measurable_splitPastTerminal).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex) := by sorry
