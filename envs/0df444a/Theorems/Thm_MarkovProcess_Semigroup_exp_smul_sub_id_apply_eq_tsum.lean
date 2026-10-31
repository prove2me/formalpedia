-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_exp_smul_sub_id_apply_eq_tsum
-- name    : MarkovProcess.Semigroup.exp_smul_sub_id_apply_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:57:22.755433+00:00
-- url     : https://prove2.me/theorems/d7af7f22-a479-451d-b6f2-a9de741c329f
-- title:
--   MarkovProcess: exp_smul_sub_id_apply_eq_tsum
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Definitions.Def_MarkovProcess_V3H_Semigroup_PoissonInvariant_3353c646
import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
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
# Poisson invariance of bounded Yosida exponentials

This file proves the uniformization argument: a normalized resolvent preserving
a closed convex set containing zero has Yosida exponentials preserving that set.
-/

open Filter Set Topology
open NormedSpace

noncomputable section

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



















namespace ContractiveResolvent

variable [CompleteSpace E]





end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Poisson invariance of bounded Yosida exponentials

This file proves the uniformization argument: a normalized resolvent preserving
a closed convex set containing zero has Yosida exponentials preserving that set.
-/

open Filter Set Topology
open NormedSpace



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]







open MarkovProcess.Semigroup in

theorem MarkovProcess.Semigroup.exp_smul_sub_id_apply_eq_tsum [CompleteSpace E]
    (Q : E →L[ℝ] E) (c : ℝ) (x : E) :
    exp (c • (Q - ContinuousLinearMap.id ℝ E)) x =
      ∑' n : ℕ, (Real.exp (-c) * (c ^ n / n.factorial)) • (Q ^ n) x := by sorry
