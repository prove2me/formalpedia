-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:15.3849+00:00
-- url     : https://prove2.me/theorems/c53eb0f3-7ccf-4959-8052-826e517a66bc
-- title:
--   MarkovProcess: isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeKernel_da0af7ef
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

open MeasureTheory ProbabilityTheory

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
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

open MeasureTheory ProbabilityTheory


variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]











open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (theta : Theta) (x : alpha) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal ↦ alpha)
      (fun I : Finset NNReal ↦ P.parameterizedFiniteSetKernel I (theta, x)) := by sorry
