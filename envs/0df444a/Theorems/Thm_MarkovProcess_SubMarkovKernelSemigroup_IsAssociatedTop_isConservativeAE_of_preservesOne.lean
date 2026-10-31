-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsAssociatedTop_isConservativeAE_of_preservesOne
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop.isConservativeAE_of_preservesOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:20.715378+00:00
-- url     : https://prove2.me/theorems/1a3ac90d-0227-4af0-a942-0e87a8c7e65b
-- title:
--   MarkovProcess: isConservativeAE_of_preservesOne
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_ConservativityAE_4ed86db4
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
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
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
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
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α]






variable (P : SubMarkovKernelSemigroup α)





open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop.isConservativeAE_of_preservesOne
    {μ : Measure α} {T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ}
    (hμ : P.IsSubInvariant μ) (hAssoc : P.IsAssociatedTop μ T)
    (hOne : PreservesOneTop μ T) : P.IsConservativeAE μ := by sorry
