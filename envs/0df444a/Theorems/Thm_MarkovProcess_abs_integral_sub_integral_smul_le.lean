-- Prove2me | Theorems.Thm_MarkovProcess_abs_integral_sub_integral_smul_le
-- name    : MarkovProcess.abs_integral_sub_integral_smul_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:23.865328+00:00
-- url     : https://prove2.me/theorems/fda17368-d4b8-410d-a1e5-e4491893a433
-- title:
--   MarkovProcess: abs_integral_sub_integral_smul_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported

namespace MarkovProcess

variable {X : Type*} [MeasurableSpace X]







end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported


variable {X : Type*} [MeasurableSpace X]



open MarkovProcess in

theorem MarkovProcess.abs_integral_sub_integral_smul_le [TopologicalSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X →ᵇ ℝ) (g : C_c(X, ℝ))
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ y, f y ∂mu) - ∫ y, (f • g) y ∂mu| ≤ ‖f‖ * (1 - ∫ y, g y ∂mu) := by sorry
