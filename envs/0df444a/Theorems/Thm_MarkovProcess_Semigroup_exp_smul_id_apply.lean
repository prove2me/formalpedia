-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_exp_smul_id_apply
-- name    : MarkovProcess.Semigroup.exp_smul_id_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:57:23.756473+00:00
-- url     : https://prove2.me/theorems/c0286024-fb08-4c8e-ac41-4cf72d143940
-- title:
--   MarkovProcess: exp_smul_id_apply
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

theorem MarkovProcess.Semigroup.exp_smul_id_apply (a : ℝ) (x : E) :
    exp (a • ContinuousLinearMap.id ℝ E) x = Real.exp a • x := by sorry
