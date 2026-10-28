-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_finiteTimeKernel_one_map_eval
-- name    : MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:48:42.498536+00:00
-- url     : https://prove2.me/theorems/a2234c25-5cf6-4a46-bbe4-5140c6ea4b23
-- title:
--   The unique coordinate of a singleton finite-time kernel has transition kernel `P` at that time
-- statement:
--   The unique coordinate of a singleton finite-time kernel has transition kernel `P` at that
--   time.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/Kernel.lean#L100-L120

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
open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-time kernels on strictly ordered time families

A conservative sub-Markov kernel semigroup determines probability kernels on finite coordinate
spaces.  The construction itself does not use a conservativity witness: it recursively samples the
first observation and then the relative tail.  Conservativity is used only to prove that the
resulting kernels are Markov kernels.

This file constructs finite-dimensional kernels only.  It makes no path-space, projectivity,
conservativity, or stochastic-process existence claim beyond the explicitly stated results.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory





variable {α : Type*} [MeasurableSpace α]

@[simp]
theorem MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval (P : SubMarkovKernelSemigroup α)
    (times : FiniteOrderedTimes 1) :
    (finiteTimeKernel P times).map (fun path ↦ path 0) = P (times 0) := by sorry
