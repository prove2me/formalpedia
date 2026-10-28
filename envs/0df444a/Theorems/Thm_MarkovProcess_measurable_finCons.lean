-- Prove2me | Theorems.Thm_MarkovProcess_measurable_finCons
-- name    : MarkovProcess.measurable_finCons
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:45:50.569443+00:00
-- url     : https://prove2.me/theorems/ca2e27a1-a42c-4290-90fc-80439cbca408
-- title:
--   Measurability of prepending a finite coordinate
-- statement:
--   For any measurable space alpha and natural number n, prepending one coordinate to an n-coordinate path produces a measurable (n+1)-coordinate path. Exact upstream statement and original proof by Scott Armstrong in MarkovProcess/FiniteTime/Kernel.lean lines 28-37 at commit 1f8060caa137731fa08029592019eeaf9d997fe5, Apache-2.0.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem MarkovProcess.measurable_finCons {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by sorry
