-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_norm_scaledOperator_apply_le
-- name    : MarkovProcess.Semigroup.ContractiveResolvent.norm_scaledOperator_apply_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:12.025572+00:00
-- url     : https://prove2.me/theorems/081593d1-54ce-4131-9651-f4de424ceeae
-- title:
--   MarkovProcess: norm_scaledOperator_apply_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/

open Filter Topology

namespace MarkovProcess.Semigroup



namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]















end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/

open Filter Topology





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





open MarkovProcess.Semigroup.ContractiveResolvent in

theorem MarkovProcess.Semigroup.ContractiveResolvent.norm_scaledOperator_apply_le (R : ContractiveResolvent E)
    (α : PositiveShift) (x : E) :
    ‖R.scaledOperator α x‖ ≤ ‖x‖ := by sorry
