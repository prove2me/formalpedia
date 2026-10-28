-- Prove2me | Theorems.Thm_MarkovProcess_measurable_finTail
-- name    : MarkovProcess.measurable_finTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:45:09.07877+00:00
-- url     : https://prove2.me/theorems/81b93a3e-861a-48fb-a016-ee8fa00e7e00
-- title:
--   Measurability of dropping the first finite coordinate
-- statement:
--   For every natural number n, dropping the first coordinate of a real-valued Fin (n+1) coordinate path defines a measurable function into the Fin n coordinate paths. Exact upstream theorem and existing proof from Scott Armstrong's MarkovProcess, commit 1f8060caa137731fa08029592019eeaf9d997fe5, MarkovProcess/Examples/BrownianMotion.lean lines 301-304 (Apache-2.0).

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

theorem MarkovProcess.measurable_finTail {n : ℕ} :
    Measurable (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) := by sorry
