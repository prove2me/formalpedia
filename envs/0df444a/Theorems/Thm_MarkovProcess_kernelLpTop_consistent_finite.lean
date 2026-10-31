-- Prove2me | Theorems.Thm_MarkovProcess_kernelLpTop_consistent_finite
-- name    : MarkovProcess.kernelLpTop_consistent_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:49.352908+00:00
-- url     : https://prove2.me/theorems/8cd9a5cf-6ebe-49e3-a289-491db2d8b1ff
-- title:
--   MarkovProcess: kernelLpTop_consistent_finite
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
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
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]







end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]





open MarkovProcess in

theorem MarkovProcess.kernelLpTop_consistent_finite
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal) [Fact (1 ≤ p)]
    (f : Lp ℝ ∞ μ) (g : Lp ℝ (p : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ p g := by sorry
