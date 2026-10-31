-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteSetKernel_map_pullback_addFinset
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_addFinset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:19.905819+00:00
-- url     : https://prove2.me/theorems/e1dcea6f-fe8b-4569-b1d5-84137d9e319d
-- title:
--   MarkovProcess: finiteSetKernel_map_pullback_addFinset
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
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
# Translation of finite dense-time kernels

This file transports the finite-set kernel translation law from physical nonnegative-real times
to finite sets of dense times, using the canonical coordinate reindexings.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
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
# Translation of finite dense-time kernels

This file transports the finite-set kernel translation law from physical nonnegative-real times
to finite sets of dense times, using the canonical coordinate reindexings.
-/

open MeasureTheory ProbabilityTheory




variable {alpha : Type*} [MeasurableSpace alpha]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_addFinset
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : DenseTime) (I : Finset DenseTime) :
    (finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
        (DenseTimePath.pullbackAddFinset s I ∘
          DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I)) =
      ((finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I)).comp
        (P (DenseTime.castOrderEmbedding s)) := by sorry
