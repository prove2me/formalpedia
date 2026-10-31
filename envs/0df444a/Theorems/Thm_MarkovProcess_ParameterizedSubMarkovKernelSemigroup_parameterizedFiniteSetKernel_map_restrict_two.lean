-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedFiniteSetKernel_map_restrict_two
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteSetKernel_map_restrict_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:38.837451+00:00
-- url     : https://prove2.me/theorems/fb220051-1613-41c7-9d99-c388c34fa2f5
-- title:
--   MarkovProcess: parameterizedFiniteSetKernel_map_restrict_two
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

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedFiniteSetKernel_map_restrict_two
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    P.parameterizedFiniteSetKernel J =
      (P.parameterizedFiniteSetKernel I).map
        (Finset.restrict₂ (π := fun _ ↦ alpha) hJI) := by sorry
