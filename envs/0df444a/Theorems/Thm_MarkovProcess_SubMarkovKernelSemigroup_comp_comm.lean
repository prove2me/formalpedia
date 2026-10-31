-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_comp_comm
-- name    : MarkovProcess.SubMarkovKernelSemigroup.comp_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:57.227978+00:00
-- url     : https://prove2.me/theorems/020f14c5-709a-45ca-ab41-b353185a7114
-- title:
--   MarkovProcess: comp_comm
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

theorem MarkovProcess.SubMarkovKernelSemigroup.comp_comm (s t : NNReal) : (P t).comp (P s) = (P s).comp (P t) := by sorry
