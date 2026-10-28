-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_backwardC0_apply_eq_integral_finiteTimeKernel
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.backwardC0_apply_eq_integral_finiteTimeKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:16:34.024371+00:00
-- url     : https://prove2.me/theorems/5a8005bb-b33e-4c0e-b51e-3bcf996b9f93
-- title:
--   Evaluation of the backward `C₀` recursion is the coordinate-product integral against the finite-time kernel
-- statement:
--   Evaluation of the backward `C₀` recursion is the coordinate-product integral against the
--   finite-time kernel.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/BackwardC0Integral.lean#L64-L125

import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-time integral represented by the backward `C₀` recursion

The backward Feller-semigroup recursion for a nonempty ordered family of `C₀` factors evaluates
to the integral of their coordinate product against the corresponding finite-time kernel.  The
proof follows the recursive kernel construction and uses composition-product integration.

No conservativity assumption is needed: sub-Markov finite-time kernels already give finite
measures, which suffice for bounded integrability.  This is an analytic identification only; no
statement about path space is proved here, and the process itself is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory ZeroAtInfty


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.backwardC0_apply_eq_integral_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) (x : alpha) :
    hP.backwardC0 times factors x =
      ∫ path, ∏ i, factors i (path i) ∂finiteTimeKernel P times x := by sorry
