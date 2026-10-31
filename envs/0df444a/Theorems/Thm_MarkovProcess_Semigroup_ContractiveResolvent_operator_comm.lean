-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_operator_comm
-- name    : MarkovProcess.Semigroup.ContractiveResolvent.operator_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:11.423339+00:00
-- url     : https://prove2.me/theorems/b65c0afc-e60f-4436-b19e-13faf3ea77ac
-- title:
--   MarkovProcess: operator_comm
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

theorem MarkovProcess.Semigroup.ContractiveResolvent.operator_comm (R : ContractiveResolvent E) (α β : PositiveShift) :
    (R.operator α).comp (R.operator β) =
      (R.operator β).comp (R.operator α) := by sorry
