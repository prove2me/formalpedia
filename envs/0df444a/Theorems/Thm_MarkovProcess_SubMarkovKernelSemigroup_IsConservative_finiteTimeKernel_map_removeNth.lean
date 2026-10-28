-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_removeNth
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_removeNth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:15:36.427503+00:00
-- url     : https://prove2.me/theorems/554644ae-df8b-412e-a8fd-fa1736e32a6d
-- title:
--   Removing one coordinate from a conservative finite-time kernel gives the kernel on the remaining ordered times
-- statement:
--   Removing one coordinate from a conservative finite-time kernel gives the kernel on the
--   remaining ordered times.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelDeletion.lean#L87-L156

import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deleting one coordinate from a finite-time kernel

For a conservative sub-Markov kernel semigroup, removing one observation from a finite-time law
gives the law on the remaining ordered times.  This is finite-dimensional kernel infrastructure;
it does not construct a path-space law or a stochastic process.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_removeNth (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (p : Fin (n + 1)) :
    (finiteTimeKernel P times).map (Fin.removeNth p) =
      finiteTimeKernel P (times.restrict (Fin.succAboveOrderEmb p)) := by sorry
