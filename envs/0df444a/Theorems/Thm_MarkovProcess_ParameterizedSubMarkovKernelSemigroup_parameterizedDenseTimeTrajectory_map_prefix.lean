-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimeTrajectory_map_prefix
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:37.789991+00:00
-- url     : https://prove2.me/theorems/4b979699-1b3e-4bca-8e04-253ca3a919dc
-- title:
--   MarkovProcess: parameterizedDenseTimeTrajectory_map_prefix
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
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

/-! # Parameterized trajectories on countable dense time -/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

universe uTheta uAlpha

variable {Theta : Type uTheta} {D : Type*} {alpha : Type uAlpha}
  [MeasurableSpace Theta] [MeasurableSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]






























































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

/-! # Parameterized trajectories on countable dense time -/

open MeasureTheory ProbabilityTheory



universe uTheta uAlpha

variable {Theta : Type uTheta} {D : Type*} {alpha : Type uAlpha}
  [MeasurableSpace Theta] [MeasurableSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]




























































open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimeTrajectory_map_prefix
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map
        (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n) =
      P.parameterizedDenseTimePrefixKernel e iota n := by sorry
