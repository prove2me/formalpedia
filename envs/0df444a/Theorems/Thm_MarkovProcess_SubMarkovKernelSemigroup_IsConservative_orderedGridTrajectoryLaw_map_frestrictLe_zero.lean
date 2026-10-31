-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_orderedGridTrajectoryLaw_map_frestrictLe_zero
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.orderedGridTrajectoryLaw_map_frestrictLe_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:31.665836+00:00
-- url     : https://prove2.me/theorems/0edae4a4-5274-4193-9df1-3299d99f0f93
-- title:
--   MarkovProcess: orderedGridTrajectoryLaw_map_frestrictLe_zero
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]



namespace OrderedGrid



end OrderedGrid





namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)



















end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

open MeasureTheory
open ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]









variable (P : SubMarkovKernelSemigroup α)

















open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.orderedGridTrajectoryLaw_map_frestrictLe_zero
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    (orderedGridTrajectoryLaw P hP grid x).map
        (fun path : ℕ → α => fun i : Finset.Iic 0 => path i) =
      Measure.dirac (initialHistory x) := by sorry
