-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_translate
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_translate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:48:31.194976+00:00
-- url     : https://prove2.me/theorems/d5687734-f677-4f5d-82d7-8fff1a911859
-- title:
--   Translating all observation times is the same as first evolving for the translation amount
-- statement:
--   Translating all observation times is the same as first evolving for the translation amount.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/KernelShift.lean#L35-L52

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
# Translation of finite-time kernels

This file proves the finite-dimensional translation identity for a conservative transition-kernel
semigroup. It is ordinary kernel infrastructure and makes no path-space or process-existence claim.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


variable {W X Y Z : Type*}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]




variable {α : Type*} [MeasurableSpace α]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_translate (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (s : NNReal) {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel P (times.translate s) = (finiteTimeKernel P times).comp (P s) := by sorry
