-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_tendsto_apply_of_opNorm_le_one
-- name    : MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:25.374464+00:00
-- url     : https://prove2.me/theorems/d73a2175-60ae-4da0-9a30-4c8f1104cb49
-- title:
--   MarkovProcess: tendsto_apply_of_opNorm_le_one
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

theorem MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by sorry
