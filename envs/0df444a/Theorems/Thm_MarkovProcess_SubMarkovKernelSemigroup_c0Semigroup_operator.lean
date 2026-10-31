-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_c0Semigroup_operator
-- name    : MarkovProcess.SubMarkovKernelSemigroup.c0Semigroup_operator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:00.51532+00:00
-- url     : https://prove2.me/theorems/b405d94c-44bb-4467-a621-1ad015ea6a36
-- title:
--   MarkovProcess: c0Semigroup_operator
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

open Topology
open scoped ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]





variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)









section Feller

variable [LocallyCompactSpace α] [T2Space α]









end Feller

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
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

open Topology
open scoped ZeroAtInfty



variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]





variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)



open MarkovProcess.SubMarkovKernelSemigroup in
@[simp]

theorem MarkovProcess.SubMarkovKernelSemigroup.c0Semigroup_operator (hTime : P.HasContinuousC0Orbits hC0) (t : NNReal) :
    (P.c0Semigroup hC0 hTime) t = P.c0Operator hC0 t := by sorry
