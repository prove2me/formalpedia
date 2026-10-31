-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimePath_pullbackPhysicalSet_apply
-- name    : MarkovProcess.DenseTimePath.pullbackPhysicalSet_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:01.844789+00:00
-- url     : https://prove2.me/theorems/862aba96-60b8-4106-af2f-decf876da023
-- title:
--   MarkovProcess: pullbackPhysicalSet_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
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
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

open SubMarkovKernelSemigroup





end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}





variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/





open SubMarkovKernelSemigroup

variable {alpha : Type*}



open MarkovProcess.DenseTimePath in
@[simp]

theorem MarkovProcess.DenseTimePath.pullbackPhysicalSet_apply (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) (t : I) :
    pullbackPhysicalSet I path t = path (DenseTime.physicalSetEquiv I t) := by sorry
