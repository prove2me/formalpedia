-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_exists_norm_yosidaStrongLimit_apply_sub_on_range_le
-- name    : MarkovProcess.Semigroup.ContractiveResolvent.exists_norm_yosidaStrongLimit_apply_sub_on_range_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:16.082342+00:00
-- url     : https://prove2.me/theorems/179f8927-55d1-4ff3-8605-af9432c49630
-- title:
--   MarkovProcess: exists_norm_yosidaStrongLimit_apply_sub_on_range_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/

open Filter NormedSpace Set Topology

noncomputable section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]













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
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/

open Filter NormedSpace Set Topology




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open MarkovProcess.Semigroup.ContractiveResolvent in

theorem MarkovProcess.Semigroup.ContractiveResolvent.exists_norm_yosidaStrongLimit_apply_sub_on_range_le
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    ∃ C : ℝ, ∀ t : NNReal,
      ‖R.yosidaStrongLimit t (R.operator mu y) - R.operator mu y‖ ≤ (t : ℝ) * C := by sorry
