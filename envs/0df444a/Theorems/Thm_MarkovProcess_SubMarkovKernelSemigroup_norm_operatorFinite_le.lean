-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_norm_operatorFinite_le
-- name    : MarkovProcess.SubMarkovKernelSemigroup.norm_operatorFinite_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:21.785236+00:00
-- url     : https://prove2.me/theorems/16c7b1cd-0ca7-46db-a81c-f2fa1cf25800
-- title:
--   MarkovProcess: norm_operatorFinite_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)





























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
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α]


variable (P : SubMarkovKernelSemigroup α)

























open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.norm_operatorFinite_le (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] (t : NNReal) :
    ‖P.operatorFinite μ hμ p t‖ ≤ 1 := by sorry
