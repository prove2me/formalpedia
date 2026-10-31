-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_comp_comm
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.comp_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:33:25.805205+00:00
-- url     : https://prove2.me/theorems/f7e5f9a0-f726-45de-b764-b58e0ee83f92
-- title:
--   MarkovProcess: comp_comm
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Mathlib.Probability.Kernel.Composition.Comp

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

open Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory



namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]





variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)





























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
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

open Set
open scoped ENNReal ProbabilityTheory



open MeasureTheory ProbabilityTheory




variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]





variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

















open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.comp_comm (theta : Theta) (s t : NNReal) :
    (P theta t).comp (P theta s) = (P theta s).comp (P theta t) := by sorry
