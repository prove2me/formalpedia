-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimeTrajectory_map_eval
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:19.413286+00:00
-- url     : https://prove2.me/theorems/b2a978fc-72fb-41af-84fd-072946de6b77
-- title:
--   MarkovProcess: parameterizedDenseTimeTrajectory_map_eval
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
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
# One-time marginals of parameterized dense-time trajectories

This file identifies every coordinate marginal of the jointly measurable parameterized
trajectory kernel.  No standard-Borel assumption is imposed on the parameter space.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]



end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-time marginals of parameterized dense-time trajectories

This file identifies every coordinate marginal of the jointly measurable parameterized
trajectory kernel.  No standard-Borel assumption is imposed on the parameter space.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_eval
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map (fun path ↦ path d) =
      P.parameterStateKernel (iota d) := by sorry
