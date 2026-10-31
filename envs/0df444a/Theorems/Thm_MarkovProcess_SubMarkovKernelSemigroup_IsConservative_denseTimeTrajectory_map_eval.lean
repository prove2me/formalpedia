-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_denseTimeTrajectory_map_eval
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:24.663225+00:00
-- url     : https://prove2.me/theorems/8f98d7cc-81c9-4b1c-aa9b-a53b77193fa5
-- title:
--   MarkovProcess: denseTimeTrajectory_map_eval
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-time marginals of the dense-time trajectory

This file identifies every coordinate marginal of the dense-time trajectory kernel with the
corresponding transition kernel.  The result is derived from the exact finite-prefix identity.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]





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
# One-time marginals of the dense-time trajectory

This file identifies every coordinate marginal of the dense-time trajectory kernel with the
corresponding transition kernel.  The result is derived from the exact finite-prefix identity.
-/

open MeasureTheory ProbabilityTheory



variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]



open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (d : D) :
    (denseTimeTrajectory P hP e ι).map (fun path ↦ path d) = P (ι d) := by sorry
