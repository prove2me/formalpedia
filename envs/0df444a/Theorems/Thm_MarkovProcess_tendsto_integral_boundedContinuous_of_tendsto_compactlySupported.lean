-- Prove2me | Theorems.Thm_MarkovProcess_tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
-- name    : MarkovProcess.tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:40.565607+00:00
-- url     : https://prove2.me/theorems/93ccab02-ba8b-47ce-abcc-aac39a8c457e
-- title:
--   MarkovProcess: tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
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

theorem MarkovProcess.tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
    [PseudoEMetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [LocallyCompactSpace X] [T2Space X] {iota : Type*} {l : Filter iota}
    (mu : iota → Measure X) (nu : Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [IsProbabilityMeasure nu]
    (h : ∀ g : C_c(X, ℝ), Tendsto (fun i ↦ ∫ y, g y ∂mu i) l (nhds (∫ y, g y ∂nu)))
    (f : X →ᵇ ℝ) : Tendsto (fun i ↦ ∫ y, f y ∂mu i) l (nhds (∫ y, f y ∂nu)) := by sorry
