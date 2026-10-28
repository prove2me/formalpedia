-- Prove2me | Theorems.Thm_MarkovProcess_tendstoUniformly_const_mul
-- name    : MarkovProcess.tendstoUniformly_const_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:40:00.716407+00:00
-- url     : https://prove2.me/theorems/70a83bd2-8647-48f3-ba7a-95ca0d453251
-- title:
--   Uniform convergence preserved by multiplication by a constant
-- statement:
--   The original theorem and complete proof from Scott Armstrong's MarkovProcess, commit 1f8060caa137731fa08029592019eeaf9d997fe5 (Apache-2.0). Uniform convergence preserved by multiplication by a constant. Source: MarkovProcess/Feller/FiniteTimeConvergence.lean, lines 50–54.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported
variable {beta : Type*} {iota : Type*} {l : Filter iota}

theorem MarkovProcess.tendstoUniformly_const_mul {F : iota → beta → ℝ} {f : beta → ℝ}
    (h : TendstoUniformly F f l) (c : ℝ) :
    TendstoUniformly (fun i x ↦ c * F i x) (fun x ↦ c * f x) l := by sorry
