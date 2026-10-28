-- Prove2me | Theorems.Thm_MarkovProcess_tendstoUniformly_const
-- name    : MarkovProcess.tendstoUniformly_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:39:57.85869+00:00
-- url     : https://prove2.me/theorems/8c205039-0185-4b4d-bad2-486bfb77c8d0
-- title:
--   Uniform convergence of a constant family
-- statement:
--   The original theorem and complete proof from Scott Armstrong's MarkovProcess, commit 1f8060caa137731fa08029592019eeaf9d997fe5 (Apache-2.0). Uniform convergence of a constant family. Source: MarkovProcess/Feller/FiniteTimeConvergence.lean, lines 45–48.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported
variable {beta : Type*} {iota : Type*} {l : Filter iota}

theorem MarkovProcess.tendstoUniformly_const (c : ℝ) :
    TendstoUniformly (fun (_ : iota) (_ : beta) ↦ c) (fun _ ↦ c) l := by sorry
