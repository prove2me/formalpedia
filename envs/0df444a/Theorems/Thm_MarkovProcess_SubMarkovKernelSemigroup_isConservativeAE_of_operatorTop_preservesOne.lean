-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_isConservativeAE_of_operatorTop_preservesOne
-- name    : MarkovProcess.SubMarkovKernelSemigroup.isConservativeAE_of_operatorTop_preservesOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:32.168396+00:00
-- url     : https://prove2.me/theorems/9e373340-805b-4b5e-a8ac-0c9e5f11dcfa
-- title:
--   MarkovProcess: isConservativeAE_of_operatorTop_preservesOne
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

theorem MarkovProcess.SubMarkovKernelSemigroup.isConservativeAE_of_operatorTop_preservesOne
    {μ : Measure α} (hμ : P.IsSubInvariant μ)
    (hOne : PreservesOneTop μ (P.operatorTop μ hμ)) :
    P.IsConservativeAE μ := by sorry
