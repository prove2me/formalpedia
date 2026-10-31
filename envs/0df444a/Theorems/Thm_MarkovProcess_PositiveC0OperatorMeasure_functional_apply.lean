-- Prove2me | Theorems.Thm_MarkovProcess_PositiveC0OperatorMeasure_functional_apply
-- name    : MarkovProcess.PositiveC0OperatorMeasure.functional_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:12.925796+00:00
-- url     : https://prove2.me/theorems/cf9193c6-62b8-4ad5-acf1-b9265d0ecdf9
-- title:
--   MarkovProcess: functional_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]





namespace PositiveC0OperatorMeasure









variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)





variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]









end PositiveC0OperatorMeasure

end MarkovProcess


open MarkovProcess
open MarkovProcess.PositiveC0OperatorMeasure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α]














variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)



open MarkovProcess.PositiveC0OperatorMeasure in
@[simp]

theorem MarkovProcess.PositiveC0OperatorMeasure.functional_apply (x : α) (f : C_c(α, ℝ)) :
    functional T hT x f = T (compactlySupportedToC0LinearMap f) x := by sorry
