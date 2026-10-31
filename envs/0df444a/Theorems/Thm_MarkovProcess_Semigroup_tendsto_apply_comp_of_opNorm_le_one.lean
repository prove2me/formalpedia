-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_tendsto_apply_comp_of_opNorm_le_one
-- name    : MarkovProcess.Semigroup.tendsto_apply_comp_of_opNorm_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:13.006513+00:00
-- url     : https://prove2.me/theorems/8014f8ae-62c2-4d4d-a6e7-fdad73ef265f
-- title:
--   MarkovProcess: tendsto_apply_comp_of_opNorm_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Normed.Operator.Completeness

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Completeness

variable [CompleteSpace E]









end Completeness





end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/

open Filter Topology


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




open MarkovProcess.Semigroup in

theorem MarkovProcess.Semigroup.tendsto_apply_comp_of_opNorm_le_one
    (T U : ℕ → E →L[ℝ] E) (Tlim Ulim : E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hTlim : ∀ x, Tendsto (fun n ↦ T n x) atTop (nhds (Tlim x)))
    (hUlim : ∀ x, Tendsto (fun n ↦ U n x) atTop (nhds (Ulim x))) (x : E) :
    Tendsto (fun n ↦ T n (U n x)) atTop (nhds (Tlim (Ulim x))) := by sorry
