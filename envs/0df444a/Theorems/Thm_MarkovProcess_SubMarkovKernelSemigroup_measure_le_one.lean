-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_measure_le_one
-- name    : MarkovProcess.SubMarkovKernelSemigroup.measure_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:37.134998+00:00
-- url     : https://prove2.me/theorems/5cf53830-07cd-4d66-9423-3f8e490870be
-- title:
--   MarkovProcess: measure_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory



namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]





variable (P : SubMarkovKernelSemigroup α)























namespace IsConservative



end IsConservative

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
# Sub-Markov transition-kernel semigroups

This file packages jointly measurable, nonnegative-time transition kernels with
the Chapman--Kolmogorov law.  Mathlib writes `η.comp κ` for first applying `κ`
and then `η`; consequently the law below is `K (s + t) = (K t).comp (K s)`.

Conservativity is deliberately a separate predicate.  A killed transition
family has mass at most one, while a conservative family has mass exactly one.
-/

open Set
open scoped ENNReal ProbabilityTheory



open MeasureTheory ProbabilityTheory




variable {α : Type*} [MeasurableSpace α]





variable (P : SubMarkovKernelSemigroup α)



















open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.measure_le_one (t : NNReal) (x : α) (s : Set α) : P t x s ≤ 1 := by sorry
