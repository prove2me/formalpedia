-- Prove2me | Theorems.Thm_MarkovProcess_PositiveC0OperatorMeasure_measure_compact_le_one
-- name    : MarkovProcess.PositiveC0OperatorMeasure.measure_compact_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:14.994222+00:00
-- url     : https://prove2.me/theorems/c2cb7b7c-8594-4dbb-ba4d-4ad2c1662f41
-- title:
--   MarkovProcess: measure_compact_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMass_48f724bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorMeasure

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)







end MarkovProcess.PositiveC0OperatorMeasure


open MarkovProcess
open MarkovProcess.PositiveC0OperatorMeasure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

open MarkovProcess.PositiveC0OperatorMeasure in

theorem MarkovProcess.PositiveC0OperatorMeasure.measure_compact_le_one (hT_norm : ‖T‖ ≤ 1) (x : α) {K : Set α} (hK : IsCompact K) :
    measure T hT x K ≤ 1 := by sorry
