-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_restrictPath
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:17:30.974445+00:00
-- url     : https://prove2.me/theorems/33cccdb0-bf69-49b8-a36a-3dcae10745f1
-- title:
--   Finite-time kernels commute with restriction of times
-- statement:
--   Restricting a conservative finite-time kernel along any finite order embedding gives the
--   kernel at the restricted times.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelRestriction.lean#L36-L83

import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
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
# Restricting finite-time kernels

For a conservative sub-Markov kernel semigroup, restriction along any finite order embedding
gives the finite-time kernel at the selected times. This is finite-dimensional kernel
infrastructure and does not construct a path-space law or a stochastic process.
-/

open ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_restrictPath
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {m n : ℕ} (times : FiniteOrderedTimes n) (e : Fin m ↪o Fin n) :
    (finiteTimeKernel P times).map (FiniteOrderedTimes.restrictPath e) =
      finiteTimeKernel P (times.restrict e) := by sorry
