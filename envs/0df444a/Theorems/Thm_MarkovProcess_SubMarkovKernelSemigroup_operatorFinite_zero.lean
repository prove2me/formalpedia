-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_operatorFinite_zero
-- name    : MarkovProcess.SubMarkovKernelSemigroup.operatorFinite_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:28.297832+00:00
-- url     : https://prove2.me/theorems/ad03dfa6-c2ba-4f92-abc8-a1b8fd7730cd
-- title:
--   MarkovProcess: operatorFinite_zero
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_OperatorSemigroup_081c0d2f
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
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
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
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α]


variable (P : SubMarkovKernelSemigroup α)













open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.operatorFinite_zero (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] :
    P.operatorFinite μ hμ p 0 = ContinuousLinearMap.id ℝ (Lp ℝ (p : ℝ≥0∞) μ) := by sorry
