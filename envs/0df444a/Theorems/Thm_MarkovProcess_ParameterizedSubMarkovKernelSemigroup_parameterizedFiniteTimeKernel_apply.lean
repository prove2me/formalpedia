-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedFiniteTimeKernel_apply
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteTimeKernel_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:48.228477+00:00
-- url     : https://prove2.me/theorems/4ec3a22e-567f-41e9-98cf-92e096ea063e
-- title:
--   MarkovProcess: parameterizedFiniteTimeKernel_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeKernel_da0af7ef
import Definitions.Def_MarkovProcess_V3H_Parameterized_OrderedGrid_cb0f8631
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-time kernels

This file constructs the finite-dimensional kernel at a fixed strictly ordered time family for a
measurably parameterized sub-Markov semigroup. The construction recursively carries the parameter
through the augmented state kernel. Fiberwise conservativity is used only for the Markov-kernel
property.

The slice theorem identifies evaluation at a parameter and start with the existing
nonparameterized finite-time kernel of the fixed-parameter semigroup. No path-space or
stochastic-process existence claim is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



















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
# Parameterized finite-time kernels

This file constructs the finite-dimensional kernel at a fixed strictly ordered time family for a
measurably parameterized sub-Markov semigroup. The construction recursively carries the parameter
through the augmented state kernel. Fiberwise conservativity is used only for the Markov-kernel
property.

The slice theorem identifies evaluation at a parameter and start with the existing
nonparameterized finite-time kernel of the fixed-parameter semigroup. No path-space or
stochastic-process existence claim is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory



variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

















open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteTimeKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) (theta : Theta) (x : alpha) :
    P.parameterizedFiniteTimeKernel times (theta, x) =
      SubMarkovKernelSemigroup.finiteTimeKernel
        (P.toSubMarkovKernelSemigroup theta) times x := by sorry
