-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_isProbabilityMeasure_parameterizedOrderedGridTrajectoryKernel_apply
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProbabilityMeasure_parameterizedOrderedGridTrajectoryKernel_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:25.411396+00:00
-- url     : https://prove2.me/theorems/3e5a8a35-1e33-4d18-8fb2-b792339602ec
-- title:
--   MarkovProcess: isProbabilityMeasure_parameterizedOrderedGridTrajectoryKernel_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized trajectory laws on a fixed ordered time grid

This file constructs a jointly measurable kernel from a parameter and starting state to the
discrete trajectory on one fixed ordered grid. The parameter is carried as a deterministic
component of an augmented state through the Ionescu--Tulcea construction, then removed from the
output path.

The result is a path-law kernel on `Theta × alpha` with values in measures on `ℕ → alpha`.
It is not a continuous-time path law and does not assert measurability in the grid.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)





















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
# Parameterized trajectory laws on a fixed ordered time grid

This file constructs a jointly measurable kernel from a parameter and starting state to the
discrete trajectory on one fixed ordered grid. The parameter is carried as a deterministic
component of an augmented state through the Ionescu--Tulcea construction, then removed from the
output path.

The result is a path-law kernel on `Theta × alpha` with values in measures on `ℕ → alpha`.
It is not a continuous-time path law and does not assert measurability in the grid.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory



variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)



















open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProbabilityMeasure_parameterizedOrderedGridTrajectoryKernel_apply
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (grid : OrderedGrid) (theta : Theta) (x : alpha) :
    IsProbabilityMeasure (P.parameterizedOrderedGridTrajectoryKernel hP grid (theta, x)) := by sorry
