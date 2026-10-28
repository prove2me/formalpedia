-- Prove2me | Theorems.Thm_MarkovProcess_map_finTail_pi
-- name    : MarkovProcess.map_finTail_pi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:00:54.631914+00:00
-- url     : https://prove2.me/theorems/8f92b11d-85e4-4834-b51d-8063ebb15442
-- title:
--   Deleting the first coordinate of a product measure preserves its remaining product law
-- statement:
--   For a finite family of probability measures on the real line, the pushforward of their product measure under Fin.tail is exactly the product of the remaining measures. This is the original theorem of Scott Armstrong, MarkovProcess/Examples/BrownianMotion.lean lines 306-320 at commit 1f8060caa137731fa08029592019eeaf9d997fe5 (Apache-2.0); it depends on the previously imported MarkovProcess.measurable_finTail.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
import Theorems.Thm_MarkovProcess_measurable_finTail

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

theorem MarkovProcess.map_finTail_pi {n : ℕ} (nu : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by sorry
