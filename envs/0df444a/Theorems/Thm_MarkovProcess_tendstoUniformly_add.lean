-- Prove2me | Theorems.Thm_MarkovProcess_tendstoUniformly_add
-- name    : MarkovProcess.tendstoUniformly_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:40:08.248114+00:00
-- url     : https://prove2.me/theorems/a51e861c-d103-47db-ac4b-e1f313dc8282
-- title:
--   Uniform convergence preserved by addition
-- statement:
--   The original theorem and complete proof from Scott Armstrong's MarkovProcess, commit 1f8060caa137731fa08029592019eeaf9d997fe5 (Apache-2.0). Uniform convergence preserved by addition. Source: MarkovProcess/Feller/FiniteTimeConvergence.lean, lines 56–60.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported
variable {beta : Type*} {iota : Type*} {l : Filter iota}

theorem MarkovProcess.tendstoUniformly_add {F G : iota → beta → ℝ} {f g : beta → ℝ}
    (hf : TendstoUniformly F f l) (hg : TendstoUniformly G g l) :
    TendstoUniformly (fun i x ↦ F i x + G i x) (fun x ↦ f x + g x) l := by sorry
