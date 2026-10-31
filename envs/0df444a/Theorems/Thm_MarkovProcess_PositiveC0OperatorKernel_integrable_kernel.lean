-- Prove2me | Theorems.Thm_MarkovProcess_PositiveC0OperatorKernel_integrable_kernel
-- name    : MarkovProcess.PositiveC0OperatorKernel.integrable_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:21.852255+00:00
-- url     : https://prove2.me/theorems/034491b1-a1b1-49be-b98f-fed87b65de39
-- title:
--   MarkovProcess: integrable_kernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_MeasurableRadonFamily_620ec0ca
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorKernel_13678038
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMass_48f724bb
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/

open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorKernel

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)















end MarkovProcess.PositiveC0OperatorKernel


open MarkovProcess
open MarkovProcess.PositiveC0OperatorKernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/

open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)











open MarkovProcess.PositiveC0OperatorKernel in

theorem MarkovProcess.PositiveC0OperatorKernel.integrable_kernel (hT_norm : ‖T‖ ≤ 1) (x : α) (f : C₀(α, ℝ)) :
    Integrable f (kernel T hT hT_norm x) := by sorry
